/* The wall walk on walls of thirty (tUrUq's method, 11-27-2026). Author of the method: Turaq Rayn-McLean.
 *
 * A wall is a multiple of 30; its eight wings are 30k + f, f in {1,7,11,13,17,19,23,29}; the mirrors 2, 3, 5
 * are the three primes off the wings. A prime block r = 30 kr + fr (kr >= 1) closes wing f of wall k exactly
 * when k = f * fr^(-1) * kr (mod r): the wall law at width 30 (Lean: FableImprovements.wall_law_width, the
 * same law as PrimeHandOff.wall_law_prime with 6 replaced by 30 and fr^(-1) in place of fr). The seven
 * blocks 7..29 are wings of wall 0 (kr = 0) and read k = -f * 30^(-1) (mod r). A wing is prime exactly when no
 * block with r*r <= seat closes it (Lean: FableImprovements.wall_walk_width). Blocks come from the walk itself.
 *
 * What is faster than wall-walk-max (walls of six, 4 bytes per seat, 2^20 walls per stretch, start positions
 * recomputed by a division for every block on every stretch):
 *   - one byte per wall of 30 (one bit per wing): 30 numbers per byte, a stretch of 2^16 walls is 64 KB and
 *     sits in the first-level cache;
 *   - the start wall of every block and wing is carried across the stretches of a chunk, no division inside;
 *   - blocks 7, 11, 13, 17 are laid once as a repeating pattern of 7*11*13*17 = 17017 walls and copied in;
 *   - blocks larger than a stretch are kept in buckets, one bucket per stretch of the chunk, each block-wing
 *     filed under the stretch it hits next, so a stretch only touches the blocks that strike inside it;
 *   - a stretch that lies wholly inside one decade is counted by popcount, not seat by seat.
 *
 *   walk TOP THREADS   every seat 2..TOP; prints prime counts at each power of ten and at TOP
 * Build: clang -O3 -o wall-walk-thirty wall-walk-thirty_v1.0_11-27-2026.c -lpthread
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <pthread.h>
#include <stdatomic.h>
#include <time.h>

typedef uint64_t u64; typedef int64_t i64; typedef uint32_t u32; typedef uint8_t u8;
#define SW 16
#define SN ((u64)1 << SW)                  /* walls per stretch */
#define PATN 17017ull                      /* 7 * 11 * 13 * 17 */
static const u32 WING[8] = {1, 7, 11, 13, 17, 19, 23, 29};

static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + t.tv_nsec * 1e-9; }

/* inverse of a modulo m (m prime to a), in [0, m) */
static u64 inv(u64 a, u64 m) {
    i64 t = 0, nt = 1; u64 r = m, nr = a % m;
    while (nr) { u64 q = r / nr; i64 tt = t - (i64)q * nt; t = nt; nt = tt; u64 rr = r - q * nr; r = nr; nr = rr; }
    return t < 0 ? (u64)(t + (i64)m) : (u64)t;
}

/* ---- blocks: the walk itself, below the root ---- */
static u32 *B; static u64 NB;              /* prime blocks >= 7 in order */
static u32 (*TSTART)[8];                   /* TSTART[b][i]: the residue of k (mod r) where block b closes wing i */
static u8 PAT[PATN];                       /* blocks 7, 11, 13, 17 laid over 17017 walls */

static void walk_blocks(u64 upto) {
    /* odd numbers 1..upto; open[m] for 2m+1; the small walk closes from r*r with the blocks it names */
    u64 n = upto / 2 + 1; u8 *open = calloc(n, 1); u64 cap = 1 << 16; B = malloc(cap * 4); NB = 0;
    for (u64 m = 1; m < n; m++) {
        if (open[m]) continue;
        u64 r = 2 * m + 1;
        if (r * r <= upto) for (u64 x = r * r; x <= upto; x += 2 * r) open[x / 2] = 1;
        if (r >= 7) { if (NB == cap) { cap *= 2; B = realloc(B, cap * 4); } B[NB++] = (u32)r; }
    }
    free(open);
    TSTART = malloc(NB * sizeof *TSTART);
    u64 agree = 0, lawful = 0;
    for (u64 b = 0; b < NB; b++) {
        u64 r = B[b], kr = r / 30, fr = r % 30, i30 = inv(30, r);
        for (int i = 0; i < 8; i++) {
            u64 f = WING[i];
            u64 t_direct = (r - f % r) % r * i30 % r;           /* k = -f * 30^(-1) */
            if (kr) {                                            /* the wall law k = f * fr^(-1) * kr */
                u64 t_law = f * inv(fr, r) % r * kr % r;
                lawful++; if (t_law == t_direct) agree++;
                TSTART[b][i] = (u32)t_law;
            } else TSTART[b][i] = (u32)t_direct;
        }
    }
    fprintf(stderr, "wall law k = f fr^-1 kr checked against k = -f 30^-1 on %llu block-wings: %llu agree\n",
            (unsigned long long)lawful, (unsigned long long)agree);
    memset(PAT, 0, PATN);
    for (u64 k = 0; k < PATN; k++) for (int i = 0; i < 8; i++) {
        u64 s = 30 * k + WING[i];
        if (s % 7 == 0 || s % 11 == 0 || s % 13 == 0 || s % 17 == 0) PAT[k] |= (u8)(1 << i);
    }
}

/* ---- walk ---- */
static u64 TOP, KMAX, NS, CH; static _Atomic u64 NEXT; static u64 NCHK; static u64 CHK[24];
static _Atomic u64 COUNT[24];
static u64 NSMALL;                          /* blocks B[0..NSMALL) are small (r <= SN), the rest go in buckets */
static u64 NBK;                             /* ring of buckets, a power of two above rmax / SN + 2 */

typedef struct { u64 k; u32 r; u32 bit; } Ent;
typedef struct { Ent *e; u64 n, cap; } Bucket;
static int ent_cmp(const void *a, const void *b) { u64 x = ((const Ent *)a)->k, y = ((const Ent *)b)->k; return x < y ? -1 : x > y; }
static inline void push(Bucket *b, u64 k, u32 r, u32 bit) {
    if (b->n == b->cap) { b->cap = b->cap ? 2 * b->cap : 1024; b->e = realloc(b->e, b->cap * sizeof(Ent)); }
    b->e[b->n].k = k; b->e[b->n].r = r; b->e[b->n].bit = bit; b->n++;
}

static void *walk_worker(void *arg) {
    (void)arg;
    u8 *S = malloc(SN);
    u64 (*nextk)[8] = malloc(NSMALL * sizeof *nextk);
    Bucket *bk = calloc(NBK, sizeof(Bucket)); Bucket far = {0, 0, 0};
    u64 *loc = calloc(NCHK, 8);
    for (;;) {
        u64 c = atomic_fetch_add(&NEXT, 1);
        if (c * CH >= NS) break;
        u64 s0 = c * CH, s1 = s0 + CH; if (s1 > NS) s1 = NS;
        u64 KC0 = s0 * SN, KC1 = s1 * SN; if (KC1 > KMAX + 1) KC1 = KMAX + 1;
        /* start walls for this chunk: one division per block, then carried */
        for (u64 b = 0; b < NB; b++) {
            u64 r = B[b]; if (r <= 17) continue;                /* in the pattern */
            u64 kc = KC0 % r;
            for (int i = 0; i < 8; i++) {
                u64 t = TSTART[b][i], k = KC0 + (t >= kc ? t - kc : t + r - kc);
                while (30 * k + WING[i] < r * r) k += r;        /* a block closes from its square */
                if (b < NSMALL) nextk[b][i] = k;
                else if (k < KC1) {
                    if (((k - KC0) >> SW) < NBK) push(&bk[((k - KC0) >> SW) & (NBK - 1)], k, (u32)r, 1u << i);
                    else push(&far, k, (u32)r, 1u << i);       /* first hit beyond the ring: a block whose square is ahead */
                }
            }
        }
        qsort(far.e, far.n, sizeof(Ent), ent_cmp); u64 fp = 0;
        for (u64 s = s0; s < s1; s++) {
            u64 K0 = s * SN, K1 = K0 + SN; if (K1 > KMAX + 1) K1 = KMAX + 1;
            u64 n = K1 - K0;
            /* the pattern of 7, 11, 13, 17 */
            u64 off = K0 % PATN, done = 0;
            while (done < n) { u64 m = PATN - off; if (m > n - done) m = n - done; memcpy(S + done, PAT + off, m); done += m; off = 0; }
            if (K0 == 0) { S[0] &= (u8)~0x1e; S[0] |= 1; }        /* 7, 11, 13, 17 are open; 1 is not a prime */
            /* small blocks, positions carried */
            for (u64 b = 0; b < NSMALL; b++) {
                u64 r = B[b]; if (r <= 17) continue;
                for (int i = 0; i < 8; i++) {
                    u64 k = nextk[b][i]; u8 bit = (u8)(1 << i);
                    for (; k < K1; k += r) S[k - K0] |= bit;
                    nextk[b][i] = k;
                }
            }
            /* far entries whose stretch has come inside the ring */
            while (fp < far.n && ((far.e[fp].k - KC0) >> SW) < (s - s0) + NBK) {
                push(&bk[((far.e[fp].k - KC0) >> SW) & (NBK - 1)], far.e[fp].k, far.e[fp].r, far.e[fp].bit); fp++;
            }
            /* large blocks from this stretch's bucket */
            Bucket *cur = &bk[(s - s0) & (NBK - 1)]; u64 cn = cur->n; cur->n = 0;
            for (u64 e = 0; e < cn; e++) {
                Ent *x = &cur->e[e]; S[x->k - K0] |= (u8)x->bit;
                u64 k = x->k + x->r;
                if (k < KC1) push(&bk[((k - KC0) >> SW) & (NBK - 1)], k, x->r, x->bit);
            }
            /* count open wings */
            u64 lo = 30 * K0 + 1, hi = 30 * (K1 - 1) + 29, j = 0;
            while (j < NCHK && lo > CHK[j]) j++;
            if (j == NCHK) continue;
            if (hi <= CHK[j]) {
                u64 open = 8 * n, w = 0;
                for (; w + 8 <= n; w += 8) { u64 x; memcpy(&x, S + w, 8); open -= (u64)__builtin_popcountll(x); }
                for (; w < n; w++) open -= (u64)__builtin_popcount(S[w]);
                loc[j] += open;
            } else {
                for (u64 w = 0; w < n && j < NCHK; w++) for (int i = 0; i < 8; i++) {
                    if (S[w] & (1 << i)) continue;
                    u64 seat = 30 * (K0 + w) + WING[i];
                    while (j < NCHK && seat > CHK[j]) j++;
                    if (j < NCHK) loc[j]++;
                }
            }
        }
        for (u64 q = 0; q < NBK; q++) bk[q].n = 0;
        far.n = 0;
    }
    for (u64 q = 0; q < NCHK; q++) atomic_fetch_add(&COUNT[q], loc[q]);
    for (u64 q = 0; q < NBK; q++) free(bk[q].e); free(far.e);
    free(bk); free(nextk); free(S); free(loc); return NULL;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: wall-walk-thirty TOP THREADS\n"); return 1; }
    int T = atoi(argv[2]); if (T < 1) T = 1; if (T > 64) T = 64;
    double t0 = now(); pthread_t th[64];
    TOP = (u64)strtod(argv[1], NULL); KMAX = TOP / 30; NS = KMAX / SN + 1;
    u64 root = (u64)sqrtl((long double)TOP) + 2;
    walk_blocks(root + 1000);
    NSMALL = 0; while (NSMALL < NB && B[NSMALL] <= SN) NSMALL++;
    u64 rmax = B[NB - 1];
    CH = NS / ((u64)T * 6); if (CH < 1) CH = 1; if (CH > 4096) CH = 4096;
    NBK = 2; while (NBK < rmax / SN + 2) NBK *= 2;
    for (u64 p = 10; p < TOP; p *= 10) CHK[NCHK++] = p;
    CHK[NCHK++] = TOP;
    fprintf(stderr, "blocks from the walk: %llu (largest %llu), %llu small, %llu buckets, %llu stretches of %llu walls, chunks of %llu, in %.1fs\n",
            (unsigned long long)NB, (unsigned long long)rmax, (unsigned long long)NSMALL, (unsigned long long)NBK,
            (unsigned long long)NS, (unsigned long long)SN, (unsigned long long)CH, now() - t0);
    atomic_store(&NEXT, 0);
    for (int i = 0; i < T; i++) pthread_create(&th[i], NULL, walk_worker, NULL);
    for (int i = 0; i < T; i++) pthread_join(th[i], NULL);
    u64 run = 3;                              /* 2, 3 and 5: the three mirrors */
    for (u64 j = 0; j < NCHK; j++) {
        run += atomic_load(&COUNT[j]);
        printf("primes <= %llu : %llu\n", (unsigned long long)CHK[j], (unsigned long long)run);
    }
    printf("walk to %llu on %d threads (walls of 30): %.1fs\n", (unsigned long long)TOP, T, now() - t0);
    return 0;
}
