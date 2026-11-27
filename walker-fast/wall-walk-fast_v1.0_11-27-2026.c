/* The fast wall walk (tUrUq's method, 11-27-2026). Author of the method: Turaq Rayn-McLean.
 *
 * Walls of 30, eight wings per wall: 30k + f, f in {1,7,11,13,17,19,23,29}; 2, 3, 5 are the three mirrors off
 * the wings. Blocks come from the walk itself. Block r = 30 kr + fr closes wing f of wall k exactly when
 * k = f * fr^(-1) * kr (mod r) (the wall law, Lean: FableImprovements.wall_law_width); the wall-0 blocks
 * 7..29 read k = -f * 30^(-1) (mod r). A wing is prime exactly when no block with r*r <= seat closes it
 * (Lean: FableImprovements.wall_walk_width).
 *
 * The walk of a block over the wings. Every seat that block r closes is r * m with m itself on a wing
 * (m = 30 j + w). As the multiplier m steps along the wings w0..w7 of its own wall j, the closures of r step
 * through the walls by kr * (w' - w) + carry, and land on wing (fr * w mod 30). Eight steps make one full
 * turn of exactly r walls. So the wall law names where a block first lands (the start), and from there the
 * block walks its own eight-step turn: no division, one state per block, not one per wing.
 *
 * What is faster than wall-walk-thirty:
 *   - large blocks: one bucket entry per block (8 bytes: kr, fr class, wall offset, which of the 8 steps),
 *     not one per wing; an entry is taken out once per stretch and walks every closure it has inside it
 *     before it is filed again. 8x fewer entries held, far fewer bucket moves for blocks below 8 stretches;
 *   - large blocks join the ring when the walk reaches their square (blocks are in order, so squares are
 *     in order): no far list, no sort;
 *   - small blocks walk their whole eight-step turn unrolled, one pointer per block, not eight wing loops;
 *     a turn that runs past the stretch spills into a back-yard carried to the next stretch, so no edge tests;
 *   - three repeating patterns laid together close 7..43 before any block walks: 7*11*13*17*19 (323323
 *     walls), 23*29*31 (20677 walls), 37*41*43 (65231 walls);
 *   - two lengths: the small blocks walk pieces of 2^17 walls (128 KB, the M4 first-level cache), the large
 *     blocks walk whole stretches of 2^20 walls (1 MB, held in the second-level cache), so a large block finds
 *     several closures each time it is taken from its bucket.
 *
 *   wall-walk-fast TOP THREADS [SW] [PW] [SMALL]   counts primes <= each power of ten and <= TOP
 *     SW: a stretch is 2^SW walls (default 20, second-level cache); the small blocks walk it in pieces of
 *     2^PW walls (default 17, first-level cache); SMALL: blocks r <= SMALL walk unrolled (default 2^PW)
 * Build: clang -O3 -mcpu=native -o wall-walk-fast wall-walk-fast_v1.0_11-27-2026.c -lpthread
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
#define PATN 323323ull                     /* 7 * 11 * 13 * 17 * 19 walls */
#define PBN 20677ull                       /* 23 * 29 * 31 walls */
#define PCN 65231ull                       /* 37 * 41 * 43 walls */
static const u32 W[9] = {1, 7, 11, 13, 17, 19, 23, 29, 31};   /* the eight wings, and 31 = next wall's 1 */
static int WIDX[30];                       /* wing number of a residue, -1 off the wings */
static u32 CO[8][9];                       /* carry: (fr * w_i) / 30, the walls gained beyond kr * w_i */
static u8 BIT[8][8];                       /* wing bit closed at step i by a block of fr class c */
static u32 DC[8][8];                       /* carry gained from step i to step i+1 */
static u32 DW[8];                          /* w_{i+1} - w_i */

static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + t.tv_nsec * 1e-9; }

static u64 inv(u64 a, u64 m) {             /* inverse of a modulo m, in [0, m) */
    i64 t = 0, nt = 1; u64 r = m, nr = a % m;
    while (nr) { u64 q = r / nr; i64 tt = t - (i64)q * nt; t = nt; nt = tt; u64 rr = r - q * nr; r = nr; nr = rr; }
    return t < 0 ? (u64)(t + (i64)m) : (u64)t;
}

/* ---- blocks: the walk itself, below the root ---- */
static u32 *B; static u64 NB, NB0;         /* blocks >= 7 in order; B[NB0..] are past the patterns (>= 47) */
static u32 (*TSTART)[8];                   /* wall law: wall residue (mod r) where block b closes wing i */
static u32 (*SC)[8];                       /* small blocks: wall offsets of the eight closures in one turn */
static u8 (*SB)[8];                        /* small blocks: the wing bit of each closure */
static u8 PAT[PATN], PB[PBN], PC[PCN];

static void walk_blocks(u64 upto) {
    u64 n = upto / 2 + 1; u8 *open = calloc(n, 1); u64 cap = 1 << 16; B = malloc(cap * 4); NB = 0;
    for (u64 m = 1; m < n; m++) {
        if (open[m]) continue;
        u64 r = 2 * m + 1; if (r > upto) break;
        if (r * r <= upto) for (u64 x = r * r; x <= upto; x += 2 * r) open[x / 2] = 1;
        if (r >= 7) { if (NB == cap) { cap *= 2; B = realloc(B, cap * 4); } B[NB++] = (u32)r; }
    }
    free(open);
    NB0 = 0; while (NB0 < NB && B[NB0] <= 43) NB0++;
    TSTART = malloc(NB * sizeof *TSTART); SC = malloc(NB * sizeof *SC); SB = malloc(NB * sizeof *SB);
    for (u64 b = 0; b < NB; b++) {
        u64 r = B[b], kr = r / 30, fr = r % 30, i30 = inv(30, r), c = (u64)WIDX[fr];
        for (int i = 0; i < 8; i++) {
            u64 f = W[i];
            TSTART[b][i] = kr ? (u32)(f * inv(fr, r) % r * kr % r)      /* the wall law k = f fr^-1 kr */
                              : (u32)((r - f % r) % r * i30 % r);        /* wall 0 blocks: k = -f 30^-1 */
            SC[b][i] = (u32)(kr * (W[i] - 1) + CO[c][i]);
            SB[b][i] = BIT[c][i];
        }
    }
    memset(PAT, 0, PATN); memset(PB, 0, PBN); memset(PC, 0, PCN);
    for (u64 k = 0; k < PATN; k++) for (int i = 0; i < 8; i++) {
        u64 s = 30 * k + W[i];
        if (s % 7 == 0 || s % 11 == 0 || s % 13 == 0 || s % 17 == 0 || s % 19 == 0) PAT[k] |= (u8)(1 << i);
        if (k < PBN && (s % 23 == 0 || s % 29 == 0 || s % 31 == 0)) PB[k] |= (u8)(1 << i);
        if (k < PCN && (s % 37 == 0 || s % 41 == 0 || s % 43 == 0)) PC[k] |= (u8)(1 << i);
    }
}

static void tables(void) {
    for (int x = 0; x < 30; x++) WIDX[x] = -1;
    for (int i = 0; i < 8; i++) WIDX[W[i]] = i;
    for (int c = 0; c < 8; c++) {
        u32 fr = W[c];
        for (int i = 0; i <= 8; i++) CO[c][i] = fr * W[i] / 30;
        for (int i = 0; i < 8; i++) { BIT[c][i] = (u8)(1u << WIDX[fr * W[i] % 30]); DC[c][i] = CO[c][i + 1] - CO[c][i]; }
    }
    for (int i = 0; i < 8; i++) DW[i] = W[i + 1] - W[i];
}

/* first closure of block b at a wall >= kfrom and at a seat >= r*r, named by the wall law;
   returns the wall, and through *step which of the eight steps of the block's turn lands there */
static u64 first_closure(u64 b, u64 kfrom, int *step) {
    u64 r = B[b], sq = r * r / 30; if (kfrom < sq) kfrom = sq;
    u64 kc = kfrom % r, best = ~0ull; int wing = 0;
    for (int i = 0; i < 8; i++) {
        u64 t = TSTART[b][i], k = kfrom + (t >= kc ? t - kc : t + r - kc);
        if (30 * k + W[i] < r * r) k += r;
        if (k < best) { best = k; wing = i; }
    }
    u64 m = (30 * best + W[wing]) / r;          /* the multiplier on its wing */
    *step = WIDX[m % 30];
    return best;
}

/* ---- walk ---- */
static u64 TOP, KMAX, NS, CH, SW, SN, PN, SMALL; static _Atomic u64 NEXT; static u64 NCHK; static u64 CHK[24];
static _Atomic u64 COUNT[24];
static u64 NSMALL, NBK;

typedef struct { u32 a, o; } Ent;            /* a = kr << 3 | fr class; o = wall offset << 3 | step */
typedef struct { Ent *e; u64 n, cap; } Bucket;
static inline void push(Bucket *b, u32 a, u32 o) {
    if (b->n == b->cap) { b->cap = b->cap ? 2 * b->cap : 4096; b->e = realloc(b->e, b->cap * sizeof(Ent)); }
    b->e[b->n].a = a; b->e[b->n].o = o; b->n++;
}

static void *walk_worker(void *arg) {
    (void)arg;
    /* the stretch with a fore-yard (turns begun before the chunk write there and are dropped) and a back-yard
       (the rest of a turn that runs past the stretch, carried into the next stretch) */
    u8 *yard = calloc(2 * SMALL + SN + 64, 1), *S = yard + SMALL, *cy = calloc(SMALL + 64, 1);
    i64 *kb = malloc(NSMALL * sizeof *kb);     /* small blocks: wall where the current turn begins */
    Bucket *bk = calloc(NBK, sizeof(Bucket));
    u64 *loc = calloc(NCHK, 8);
    for (;;) {
        u64 c = atomic_fetch_add(&NEXT, 1);
        if (c * CH >= NS) break;
        u64 s0 = c * CH, s1 = s0 + CH; if (s1 > NS) s1 = NS;
        u64 KC0 = s0 * SN;
        for (u64 b = NB0; b < NSMALL; b++) {   /* small blocks: the turn holding the first closure */
            int st; u64 k = first_closure(b, KC0, &st);
            kb[b] = (i64)k - (i64)SC[b][st] - (i64)KC0;
        }
        memset(cy, 0, SMALL); memset(S + SN, 0, SMALL);
        u64 act = NSMALL;                       /* next large block to join, in order of squares */
        for (u64 s = s0; s < s1; s++) {
            u64 K0 = s * SN, K1 = K0 + SN; if (K1 > KMAX + 1) K1 = KMAX + 1;
            u64 n = K1 - K0;
            /* three repeating patterns laid together: 7..19, 23 29 31, 37 41 43 */
            u64 oa = K0 % PATN, ob = K0 % PBN, oc = K0 % PCN, done = 0;
            while (done < n) {
                u64 m = n - done;
                if (m > PATN - oa) m = PATN - oa;
                if (m > PBN - ob) m = PBN - ob;
                if (m > PCN - oc) m = PCN - oc;
                const u8 *a = PAT + oa, *bb = PB + ob, *cc = PC + oc; u8 *d = S + done;
                for (u64 i = 0; i < m; i++) d[i] = a[i] | bb[i] | cc[i];
                done += m; oa += m; ob += m; oc += m;
                if (oa == PATN) oa = 0;
                if (ob == PBN) ob = 0;
                if (oc == PCN) oc = 0;
            }
            if (K0 == 0) { S[0] = 1; S[1] &= (u8)~0x0f; }   /* 7..29 and 31, 37, 41, 43 are open; 1 is not a prime */
            for (u64 i = 0; i < SMALL; i++) S[i] |= cy[i];   /* turns carried from the stretch before */
            /* small blocks, piece by piece: every turn begun in a piece is walked whole, unrolled */
            for (u64 p0 = 0; p0 < n; p0 += PN) {
            i64 pe = (i64)(p0 + PN < n ? p0 + PN : n), shift = pe == (i64)n ? (i64)n : 0;
            for (u64 b = NB0; b < NSMALL; b++) {
                i64 r = B[b], k = kb[b]; const u32 *o = SC[b]; const u8 *t = SB[b];
                u32 o1 = o[1], o2 = o[2], o3 = o[3], o4 = o[4], o5 = o[5], o6 = o[6], o7 = o[7];
                u8 t0 = t[0], t1 = t[1], t2 = t[2], t3 = t[3], t4 = t[4], t5 = t[5], t6 = t[6], t7 = t[7];
                for (; k < pe; k += r) {
                    u8 *p = S + k;
                    p[0] |= t0; p[o1] |= t1; p[o2] |= t2; p[o3] |= t3; p[o4] |= t4; p[o5] |= t5; p[o6] |= t6; p[o7] |= t7;
                }
                kb[b] = k - shift;
            }
            }
            memcpy(cy, S + n, SMALL); memset(S + n, 0, SMALL);   /* the back-yard goes to the next stretch */
            /* large blocks whose square the walk has now reached join the ring */
            while (act < NB && (u64)B[act] * B[act] / 30 < K1) {
                int st; u64 k = first_closure(act, K0, &st), r = B[act];
                if ((k >> SW) < s1) push(&bk[(k >> SW) & (NBK - 1)], (u32)((r / 30) << 3 | (u64)WIDX[r % 30]), (u32)((k & (SN - 1)) << 3 | (u64)st));
                act++;
            }
            /* large blocks from this stretch's bucket: each walks all its closures here, then is filed again */
            Bucket *cur = &bk[s & (NBK - 1)]; u64 cn = cur->n; cur->n = 0;
            for (u64 e = 0; e < cn; e++) {
                u32 a = cur->e[e].a, kr = a >> 3, cl = a & 7;
                u64 x = cur->e[e].o >> 3; u32 st = cur->e[e].o & 7;
                do { S[x] |= BIT[cl][st]; x += kr * DW[st] + DC[cl][st]; st = (st + 1) & 7; } while (x < n);
                u64 ns = s + (x >> SW);
                if (ns > s && ns < s1) push(&bk[ns & (NBK - 1)], a, (u32)((x & (SN - 1)) << 3 | st));
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
                    u64 seat = 30 * (K0 + w) + W[i];
                    while (j < NCHK && seat > CHK[j]) j++;
                    if (j < NCHK) loc[j]++;
                }
            }
        }
        for (u64 q = 0; q < NBK; q++) bk[q].n = 0;
    }
    for (u64 q = 0; q < NCHK; q++) atomic_fetch_add(&COUNT[q], loc[q]);
    for (u64 q = 0; q < NBK; q++) free(bk[q].e);
    free(bk); free(kb); free(yard); free(cy); free(loc); return NULL;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: wall-walk-fast TOP THREADS [SW] [PW] [SMALL]\n"); return 1; }
    int T = atoi(argv[2]); if (T < 1) T = 1; if (T > 64) T = 64;
    SW = argc > 3 ? (u64)atoi(argv[3]) : 20; if (SW < 10 || SW > 24) SW = 20;
    SN = 1ull << SW;
    u64 PW = argc > 4 ? (u64)atoi(argv[4]) : 17; if (PW > SW) PW = SW;
    PN = 1ull << PW;
    SMALL = argc > 5 ? (u64)strtod(argv[5], NULL) : PN;
    if (SMALL > SN) SMALL = SN;               /* a small turn must fit in one back-yard */
    double t0 = now(); pthread_t th[64];
    tables();
    TOP = (u64)strtod(argv[1], NULL); KMAX = TOP / 30; NS = KMAX / SN + 1;
    u64 root = (u64)sqrtl((long double)TOP) + 2;
    walk_blocks(root + 1000);
    /* check: the wall law start and the block's own eight-step turn name the same closure, on every block-wing */
    u64 agree = 0, tried = 0;
    for (u64 b = NB0; b < NB; b++) {
        u64 r = B[b], c = (u64)WIDX[r % 30];
        for (int i = 0; i < 8; i++) {
            u64 m = 30 * (r / 30 + 1 + (u64)i) + W[i];                     /* a multiplier on each wing in turn */
            u64 k = r * m / 30, f = r * m % 30; int wi = WIDX[f], st = WIDX[m % 30];
            tried++; if (k % r == TSTART[b][wi] && BIT[c][st] == (1u << wi) && k == r * (m / 30) + r / 30 + SC[b][st] - CO[c][0]) agree++;
            else fprintf(stderr, "disagree r=%llu m=%llu\n", (unsigned long long)r, (unsigned long long)m);
        }
    }
    fprintf(stderr, "wall law against the eight-step turn on %llu block-wings: %llu agree\n", (unsigned long long)tried, (unsigned long long)agree);
    if (agree != tried) return 2;
    NSMALL = NB0; while (NSMALL < NB && B[NSMALL] <= SMALL) NSMALL++;
    u64 rmax = B[NB - 1];
    CH = NS / ((u64)T * 6); if (CH < 1) CH = 1; if (CH > 4096) CH = 4096;
    u64 maxstep = 6 * (rmax / 30) + 30;
    NBK = 2; while (NBK < maxstep / SN + 2) NBK *= 2;
    for (u64 p = 10; p < TOP; p *= 10) CHK[NCHK++] = p;
    CHK[NCHK++] = TOP;
    fprintf(stderr, "blocks from the walk: %llu (largest %llu), %llu small, %llu buckets, %llu stretches of %llu walls in pieces of %llu, chunks of %llu, in %.1fs\n",
            (unsigned long long)NB, (unsigned long long)rmax, (unsigned long long)(NSMALL - NB0), (unsigned long long)NBK,
            (unsigned long long)NS, (unsigned long long)SN, (unsigned long long)PN, (unsigned long long)CH, now() - t0);
    atomic_store(&NEXT, 0);
    for (int i = 0; i < T; i++) pthread_create(&th[i], NULL, walk_worker, NULL);
    for (int i = 0; i < T; i++) pthread_join(th[i], NULL);
    u64 run = 3;                              /* 2, 3 and 5: the three mirrors */
    for (u64 j = 0; j < NCHK; j++) {
        run += atomic_load(&COUNT[j]);
        printf("primes <= %llu : %llu\n", (unsigned long long)CHK[j], (unsigned long long)run);
    }
    printf("walk to %llu on %d threads (fast walls of 30): %.2fs\n", (unsigned long long)TOP, T, now() - t0);
    return 0;
}
