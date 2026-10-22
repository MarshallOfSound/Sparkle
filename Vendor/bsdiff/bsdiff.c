/*-
 * Copyright 2003 - 2005 Colin Percival
 * All rights reserved
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted providing that the following conditions 
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING
 * IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 */

#if 0
__FBSDID("$FreeBSD: src/usr.bin/bsdiff/bsdiff/bsdiff.c, v 1.1 2005/08/06 01:59:05 cperciva Exp $");
#endif

#include <sys/types.h>
#include "sais.h"

#include <err.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "bscommon.h"
#include <stdint.h>
#include <sys/mman.h>
#include <sys/stat.h>

/* Files at least this big use a sampled hash index instead of a suffix array:
 * no sort, a fraction of the memory, and one probe per position instead of a
 * binary search. Patches stay valid but can be slightly larger. */
#define HASH_INDEX_MIN_SIZE (1 << 20)
#define HASH_STRIDE 2
#define HASH_WAYS 8
#define HASH_KEY_MASK 0xFFFFFFFFFFFFull /* 6 bytes */
#define HASH_READ_SIZE 8
/* Bounds match checking per scanned byte, so repetitive data stays linear
 * whichever index found the matches. */
#define SEARCH_WORK_PER_BYTE 16
#define SEARCH_WORK_SLACK (1 << 16)
/* Extending matches is normally cheap. Past this budget, repetitive data has
 * made it dominate, so each extension's reach is capped. */
#define EXTEND_WORK_PER_BYTE 64
#define EXTEND_WORK_SLACK (1 << 26)
#define EXTEND_CAPPED_REACH 4096

typedef struct {
    uint32_t *slots;
    uint64_t buckets;
} hash_index;

/* Big buffers skip malloc, which keeps freed large blocks resident in its cache. */
static void *big_alloc(size_t size)
{
    void *p = mmap(NULL, size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, -1, 0);
    return (p == MAP_FAILED) ? NULL : p;
}

static void big_free(void *p, size_t size)
{
    if (p != NULL)
        munmap(p, size);
}

/* An empty file gets a one-byte anonymous mapping, so callers can always unmap. */
static u_char *map_file(const char *path, off_t *size)
{
    struct stat st;
    void *p;
    int fd = open(path, O_RDONLY);

    if (fd < 0)
        return NULL;
    if (fstat(fd, &st) != 0) {
        close(fd);
        return NULL;
    }
    *size = st.st_size;
    if (st.st_size == 0) {
        close(fd);
        return big_alloc(1);
    }
    p = mmap(NULL, (size_t)st.st_size, PROT_READ, MAP_PRIVATE, fd, 0);
    close(fd);
    return (p == MAP_FAILED) ? NULL : p;
}

static void unmap_file(u_char *p, off_t size)
{
    big_free(p, size ? (size_t)size : 1);
}

static inline uint64_t hash_key(const u_char *p)
{
    uint64_t v;
    memcpy(&v, p, HASH_READ_SIZE);
    return v & HASH_KEY_MASK;
}

static inline uint32_t *hash_bucket(const hash_index *h, uint64_t key)
{
    uint64_t mixed = key * 0x9E3779B97F4A7C15ull;
    return h->slots + (uint64_t)(((__uint128_t)mixed * h->buckets) >> 64) * HASH_WAYS;
}

static size_t hash_bytes(const hash_index *h)
{
    return (size_t)h->buckets * HASH_WAYS * sizeof(uint32_t);
}

static int hash_build(hash_index *h, const u_char *old, off_t oldsize)
{
    h->buckets = (uint64_t)(oldsize / HASH_STRIDE + 1) / HASH_WAYS + 1;
    if ((h->slots = big_alloc(hash_bytes(h))) == NULL)
        return -1;

    /* Positions are stored as 32-bit values, offset by one so 0 means empty. */
    for (off_t i = 0; i + HASH_READ_SIZE <= oldsize && i < UINT32_MAX; i += HASH_STRIDE) {
        uint32_t *bucket = hash_bucket(h, hash_key(old + i));
        /* Keep the earliest positions: in repetitive data, later ones hit the end of the file and give short matches. */
        for (unsigned w = 0; w < HASH_WAYS; w++) {
            if (bucket[w] == 0) {
                bucket[w] = (uint32_t)i + 1;
                break;
            }
        }
    }
    return 0;
}

static off_t matchlen(u_char *old, off_t oldsize, u_char *newp, off_t newsize);

/* Longest match among the bucket's candidates, preferring the one closest to
 * 'expected' on ties. Returns 0 if there is none. */
static off_t hash_search(const hash_index *h, u_char *old, off_t oldsize,
        u_char *newp, off_t newsize, off_t expected, off_t *pos)
{
    off_t best = 0, bestdistance = 0;
    uint64_t key;
    const uint32_t *bucket;

    if (newsize < HASH_READ_SIZE)
        return 0;

    key = hash_key(newp);
    bucket = hash_bucket(h, key);
    for (unsigned w = 0; w < HASH_WAYS && bucket[w] != 0; w++) {
        off_t candidate = (off_t)bucket[w] - 1;
        off_t length, distance;

        if (hash_key(old + candidate) != key)
            continue;
        length = matchlen(old + candidate, oldsize - candidate, newp, newsize);
        distance = (candidate > expected) ? candidate - expected : expected - candidate;
        if (length > best || (length == best && distance < bestdistance)) {
            best = length;
            bestdistance = distance;
            *pos = candidate;
        }
    }
    return best;
}

#define MIN(x, y) (((x)<(y)) ? (x) : (y))

/* matchlen(old, oldsize, new, newsize)
 *
 * Returns the length of the longest common prefix between 'old' and 'new'. */
static off_t matchlen(u_char *old, off_t oldsize, u_char *newp, off_t newsize)
{
    off_t i;

    for (i = 0; (i < oldsize) && (i < newsize); i++)
    {
        if (old[i] != newp[i])
            break;
    }

    return i;
}

/* search(I, old, oldsize, new, newsize, st, en, pos)
 *
 * Searches for the longest prefix of 'new' that occurs in 'old', stores its
 * offset in '*pos', and returns its length. 'I' should be the suffix sort of
 * 'old', and 'st' and 'en' are the lowest and highest indices in the suffix
 * sort to consider. If you're searching all suffixes, 'st = 0' and 'en =
 * oldsize - 1'. */
static off_t search(int *I, u_char *old, off_t oldsize,
        u_char *newp, off_t newsize, off_t st, off_t en, off_t *pos)
{
    off_t x, y;

    if (en - st < 2) {
        x = matchlen(old + I[st], oldsize - I[st], newp, newsize);
        y = matchlen(old + I[en], oldsize - I[en], newp, newsize);

        if (x > y) {
            *pos = I[st];
            return x;
        } else {
            *pos = I[en];
            return y;
        }
    }

    x = st + (en - st)/2;
    /* Modification ported from ChromiumOS project:
     * https://chromium.googlesource.com/chromiumos/third_party/bsdiff/+/58146f74abd6b1b69693943195f37f4ac6a6acef%5E%21/#F0 */
    if (memcmp(old + I[x], newp, (size_t)(MIN(oldsize - I[x], newsize))) <= 0) {
        return search(I, old, oldsize, newp, newsize, x, en, pos);
    } else {
        return search(I, old, oldsize, newp, newsize, st, x, pos);
    }
}

/* offtout(x, buf)
 * 
 * Writes the off_t 'x' portably to the array 'buf'. */
static void offtout(off_t x, u_char *buf)
{
    off_t y;

    if (x < 0)
        y = -x;
    else
        y = x;

    buf[0] = (u_char)(y % 256);
    y -= buf[0];
    y = y/256; buf[1] = (u_char)(y%256); y -= buf[1];
    y = y/256; buf[2] = (u_char)(y%256); y -= buf[2];
    y = y/256; buf[3] = (u_char)(y%256); y -= buf[3];
    y = y/256; buf[4] = (u_char)(y%256); y -= buf[4];
    y = y/256; buf[5] = (u_char)(y%256); y -= buf[5];
    y = y/256; buf[6] = (u_char)(y%256); y -= buf[6];
    y = y/256; buf[7] = (u_char)(y%256);

    if (x < 0)
        buf[7] |= 0x80;
}

int bsdiff(int argc, char *argv[]); // Added by AMM: suppresses a warning about the following not having a prototype.

int bsdiff(int argc, char *argv[])
{
    u_char *old = NULL,*newp = NULL;           /* contents of old, new files */
    off_t oldsize = 0, newsize = 0;     /* length of old, new files */
    int *I = NULL;                  /* suffix sort of old, for small files; I is ordering */
    size_t Ibytes = 0;              /* size of I */
    hash_index H = {0};             /* sampled index of old, for large files */
    int usehash = 0;
    off_t prev_len = 0, prev_oldscore = 0, prev_pos = 0;
    off_t extendwork = 0, reach = 0;
    off_t mappednewsize = 0;        /* newsize is reused as scratch below */
    off_t scan = 0;                 /* position of current match in old file */
    off_t pos = 0;              /* position of current match in new file */
    off_t len = 0;                  /* length of current match */
    off_t lastscan = 0;             /* position of previous match in old file */
    off_t lastpos = 0;              /* position of previous match in new file */
    off_t lastoffset = 0;           /* lastpos - lastscan */
    off_t oldscore = 0, scsc = 0;       /* temp variables in match search */
    off_t s = 0, Sf = 0, lenf = 0, Sb = 0, lenb = 0;    /* temp vars in match extension */
    off_t overlap = 0, Ss = 0, lens = 0;
    off_t i = 0;
    off_t dblen = 0, eblen = 0;         /* length of diff, extra sections */
    u_char *db = NULL,*eb = NULL;             /* contents of diff, extra sections */
    u_char buf[8] = {0};
    u_char header[32] = {0};
    FILE * pf = NULL;
    int exitstatus = -1;

    if (argc != 4) {
        warnx("usage: %s oldfile newfile patchfile\n", argv[0]);
        goto cleanup;
    }

    old = map_file(argv[1], &oldsize);
    if (old == NULL) {
        warn("old file error: %s", argv[1]);
        goto cleanup;
    }

    usehash = oldsize >= HASH_INDEX_MIN_SIZE;
    if (usehash) {
        if (hash_build(&H, old, oldsize) != 0) {
            warn("Failed to allocate memory for hash index");
            goto cleanup;
        }
    } else {
        Ibytes = ((size_t)oldsize + 1) * sizeof(int);
        if ((I = big_alloc(Ibytes)) == NULL) {
            warn("Failed to allocate memory for I");
            goto cleanup;
        }

        /* Do a suffix sort on the old file. */
        I[0] = (int)oldsize;
        if (sais(old, I+1, (int)oldsize) != 0) {
            warn("Failed to sort %s", argv[1]);
            goto cleanup;
        }
    }

    newp = map_file(argv[2], &newsize);
    mappednewsize = newsize;
    if (newp == NULL) {
        warn("new file error: %s", argv[2]);
        goto cleanup;
    }

    if (((db = big_alloc((size_t)newsize + 1)) == NULL) ||
        ((eb = big_alloc((size_t)newsize + 1)) == NULL)) {
        warn("Failed to allocate memory for db or eb");
        goto cleanup;
    }
    dblen = 0;
    eblen = 0;

    /* Create the patch file */
    if ((pf = fopen(argv[3], "w")) == NULL) {
        warn("%s", argv[3]);
        goto cleanup;
    }

    /* Header is
        0    8     "BSDIFN40"
        8    8    length of ctrl block
        16    8    length of diff block
        24    8    length of new file */
    /* File is
        0    32    Header
        32    ??    ctrl block
        ??    ??    diff block
        ??    ??    extra block */
    memcpy(header, "BSDIFN40", 8);
    offtout(0, header + 8);
    offtout(0, header + 16);
    offtout(newsize, header + 24);
    if (fwrite(header, 32, 1, pf) != 1) {
        warn("fwrite(%s)", argv[3]);
        goto cleanup;
    }

    /* Compute the differences, writing ctrl as we go */
    scan = 0;
    len = 0;
    lastscan = 0;
    lastpos = 0;
    lastoffset = 0;
    while (scan < newsize) {
        oldscore = 0;
        /* Modification ported from ChromiumOS project:
         * https://chromium.googlesource.com/chromiumos/third_party/bsdiff/+/a055996c743add7a9558839276fd1e4994d16bd3%5E%21/#F0 */
        /* If we come across a large block of data that only differs
         * by less than 8 bytes, this loop will take a long time to
         * go past that block of data. We need to track the number of
         * times we're stuck in the block and break out of it. */
        int num_less_than_eight = 0;
        off_t searchwork = 0, searchstart = scan + len;
        for (scsc = scan += len; scan < newsize; scan++) {
            /* A sampled index misses at positions with no entry, reporting len 0
             * with a stale pos. Misses must not disturb the stuck-block guard. */
            if (!usehash || len != 0) {
                prev_len = len;
                prev_oldscore = oldscore;
                prev_pos = pos;
            }
            /* 'oldscore' is the number of characters that match between the
             * substrings 'old[lastoffset + scan:lastoffset + scsc]' and
             * 'new[scan:scsc]'. */
            if (usehash) {
                len = hash_search(&H, old, oldsize, newp + scan, newsize - scan,
                        lastoffset + scan, &pos);
            } else {
                len = search(I, old, oldsize, newp + scan, newsize - scan,
                        0, oldsize, &pos);
            }

            /* If this match extends further than the last one, add any new
             * matching characters to 'oldscore'. */
            for (; scsc < scan + len; scsc++) {
                if ((scsc + lastoffset < oldsize) &&
                    (old[scsc + lastoffset] == newp[scsc]))
                    oldscore++;
            }

            /* Choose this as our match if it contains more than eight
             * characters that would be wrong if matched with a forward
             * extension of the previous match instead. */
            if ((len != 0) && ((len == oldscore) || (len > oldscore + 8)))
                break;

            searchwork += len;
            if (searchwork > (scan - searchstart) * SEARCH_WORK_PER_BYTE + SEARCH_WORK_SLACK)
                break;

            /* Since we're advancing 'scan' by 1, remove the character under it
             * from 'oldscore' if it matches. */
            if ((scan + lastoffset < oldsize) &&
                (old[scan + lastoffset] == newp[scan]))
                oldscore--;

            /* Modification ported from ChromiumOS project:
             * https://chromium.googlesource.com/chromiumos/third_party/bsdiff/+/426e4aa1cbeb3c8a73002047d7a796ca8e5e17d4%5E%21/#F0 */
            const off_t fuzz = 8;
            if (usehash && len == 0)
                continue;
            if (prev_len - fuzz <= len && len <= prev_len &&
                prev_oldscore - fuzz <= oldscore &&
                oldscore <= prev_oldscore &&
                prev_pos <= pos && pos <= prev_pos + fuzz &&
                oldscore <= len && len <= oldscore + fuzz)
                ++num_less_than_eight;
            else
                num_less_than_eight=0;
            if (num_less_than_eight > 100) break;
        }

        /* Skip this section if we found an exact match that would be
         * better serviced by a forward extension of the previous match. */
        if ((len != oldscore) || (scan == newsize)) {
            /* Figure out how far forward the previous match should be
             * extended... */
            s = 0;
            Sf = 0;
            lenf = 0;
            reach = scan - lastscan;
            if (extendwork > newsize * EXTEND_WORK_PER_BYTE + EXTEND_WORK_SLACK)
                reach = MIN(reach, EXTEND_CAPPED_REACH);
            extendwork += reach;
            for (i = 0; (i < reach) && (lastpos + i < oldsize);) {
                if (old[lastpos + i] == newp[lastscan + i])
                    s++;
                i++;
                if (s * 2 - i > Sf * 2 - lenf) {
                    Sf = s;
                    lenf = i;
                }
            }

            /* ... and how far backwards the next match should be extended. */
            lenb = 0;
            if (scan < newsize) {
                s = 0;
                Sb = 0;
                for (i = 1; (i <= reach) && (pos >= i); i++) {
                    if (old[pos - i] == newp[scan - i])
                        s++;
                    if (s * 2 - i > Sb * 2 - lenb) {
                        Sb = s;
                        lenb = i;
                    }
                }
            }

            /* If there is an overlap between the extensions, find the best
             * dividing point in the middle and reset 'lenf' and 'lenb'
             * accordingly. */
            if (lastscan + lenf > scan - lenb) {
                overlap = (lastscan + lenf) - (scan - lenb);
                s = 0;
                Ss = 0;
                lens = 0;
                for (i = 0; i < overlap; i++) {
                    if (newp[lastscan + lenf - overlap + i] ==
                        old[lastpos + lenf - overlap + i])
                        s++;
                    if (newp[scan - lenb + i] == old[pos - lenb + i])
                        s--;
                    if (s > Ss) {
                        Ss = s;
                        lens = i + 1;
                    }
                }

                lenf += lens - overlap;
                lenb -= lens;
            }

            /* Write the diff data for the last match to the diff section... */
            for (i = 0; i < lenf; i++)
                db[dblen + i] = newp[lastscan + i] - old[lastpos + i];
            /* ... and, if there's a gap between the extensions just
             * calculated, write the data in that gap to the extra section. */
            for (i = 0; i< (scan - lenb) - (lastscan + lenf); i++)
                eb[eblen + i] = newp[lastscan + lenf + i];

            /* Update the diff and extra section lengths accordingly. */
            dblen += lenf;
            eblen += (scan - lenb) - (lastscan + lenf);

            /* Write the following triple of integers to the control section:
             *  - length of the diff
             *  - length of the extra section
             *  - offset between the end of the diff and the start of the next
             *      diff, in the old file
             */
            offtout(lenf, buf);
            if (fwrite(buf, 8, 1, pf) != 1) {
                warnx("fwrite");
                goto cleanup;
            }

            offtout((scan - lenb) - (lastscan + lenf), buf);
            if (fwrite(buf, 8, 1, pf) != 1) {
                warn("fwrite");
                goto cleanup;
            }

            offtout((pos - lenb) - (lastpos + lenf), buf);
            if (fwrite(buf, 8, 1, pf) != 1) {
                warn("fwrite");
                goto cleanup;
            }

            /* Update the variables describing the last match. Note that
             * 'lastscan' is set to the start of the current match _after_ the
             * backwards extension; the data in that extension will be written
             * in the next pass. */
            lastscan = scan - lenb;
            lastpos = pos - lenb;
            lastoffset = pos - scan;
        }
    }

    /* Compute size of compressed ctrl data */
    if ((len = ftello(pf)) == -1) {
        warn("ftello");
        goto cleanup;
    }
    offtout(len - 32, header + 8);

    /* Write diff data */
    if (dblen && fwrite(db, (size_t)dblen, 1, pf) != 1) {
        warn("fwrite");
        goto cleanup;
    }

    /* Compute size of compressed diff data */
    if ((newsize = ftello(pf)) == -1) {
        warn("ftello");
        goto cleanup;
    }
    offtout(newsize - len, header + 16);

    /* Write extra data */
    if (eblen && fwrite(eb, (size_t)eblen, 1, pf) != 1) {
        warn("fwrite");
        goto cleanup;
    }

    /* Seek to the beginning, write the header, and close the file */
    if (fseeko(pf, 0, SEEK_SET)) {
        warn("fseeko");
        goto cleanup;
    }
    if (fwrite(header, 32, 1, pf) != 1) {
        warn("fwrite(%s)", argv[3]);
        goto cleanup;
    }
    if (fclose(pf)) {
        warn("fclose");
        pf = NULL;
        goto cleanup;
    }
    pf = NULL;
    
    exitstatus = 0;
cleanup:

    if (pf != NULL) {
        fclose(pf);
    }
    
    /* Free the memory we used */
    big_free(db, (size_t)mappednewsize + 1);
    big_free(eb, (size_t)mappednewsize + 1);
    big_free(I, Ibytes);
    if (H.slots != NULL)
        big_free(H.slots, hash_bytes(&H));
    if (old != NULL)
        unmap_file(old, oldsize);
    if (newp != NULL)
        unmap_file(newp, mappednewsize);

    return exitstatus;
}
