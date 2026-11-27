/* The wall walk at full speed (tUrUq's method, 11-27-2026). Author of the method: Turaq Rayn-McLean.
 * Seats beside walls: 6k-1 and 6k+1. A prime block r = 6kr + fr closes wing f of wall k exactly when
 * k = f*fr*kr (mod r) (Lean: PrimeHandOff.wall_law_prime); a seat is prime exactly when no block with
 * r*r <= seat closes it (Lean: WallWalk.wall_walk). Blocks come from the walk itself, starting from 2 and 3.
 *
 *   walk  TOP THREADS      every seat 2..TOP; prints prime counts at each power of ten and at TOP
 *   edge  SEATS THREADS    the last SEATS/2 walls below 2^64; every named prime checked by two separate
 *                          Miller-Rabin base sets, every closed seat by its dividing block
 * Build: clang -O3 -o wall-walk-max wall-walk-max_v1.0_11-27-2026.c -lpthread
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <pthread.h>
#include <stdatomic.h>
#include <time.h>

typedef uint64_t u64; typedef int64_t i64; typedef unsigned __int128 u128;
#define L (1u << 20)                       /* walls per stretch */

static u64 *B; static u64 NB;              /* blocks named by the walk, in order */
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + t.tv_nsec * 1e-9; }

/* lay blocks B[0..nb) over walls K0..K0+n-1; lo/hi get the closing block (0 = open) */
static void close_walls(u64 K0, u64 n, u64 nb, uint32_t *lo, uint32_t *hi, int own) {
    memset(lo, 0, n * 4); memset(hi, 0, n * 4);
    for (u64 i = nb; i-- > 0;) {            /* largest first, so the smallest block is written last */
        u64 r = B[i]; i64 kr = (i64)((r + 1) / 6), fr = (i64)r - 6 * kr;
        u64 K0r = K0 % r;
        for (int f = -1; f <= 1; f += 2) {
            uint32_t *a = f < 0 ? lo : hi;
            i64 t = ((i64)f * fr * kr) % (i64)r; if (t < 0) t += r;
            i64 x = t - (i64)K0r; if (x < 0) x += r;
            if (own && f == fr && K0 + (u64)x == (u64)kr) x += r;
            for (u64 y = (u64)x; y < n; y += r) a[y] = (uint32_t)r;
        }
    }
}

/* the walk from 2 and 3 alone, up to seat 'upto' (kept in memory as blocks) */
static void walk_blocks(u64 upto) {
    u64 cap = 1 << 20; B = malloc(cap * 8); NB = 0;
    uint32_t *lo = malloc(L * 4), *hi = malloc(L * 4);
    u64 K = 1, KMAX = (upto + 1) / 6;
    while (K <= KMAX) {
        u64 top = NB ? B[NB - 1] : 0;
        u64 K1 = K + L; if (K1 > KMAX + 1) K1 = KMAX + 1;
        u64 lim = top ? (top * top + 1) / 6 + 1 : 4; if (K1 > lim) K1 = lim;
        u64 n = K1 - K, maxs = 6 * (K1 - 1) + 1, nb = 0;
        while (nb < NB && B[nb] * B[nb] <= maxs) nb++;
        close_walls(K, n, nb, lo, hi, 1);
        for (u64 i = 0; i < n; i++) {
            if (NB + 2 > cap) { cap *= 2; B = realloc(B, cap * 8); }
            if (!lo[i]) B[NB++] = 6 * (K + i) - 1;
            if (!hi[i]) B[NB++] = 6 * (K + i) + 1;
        }
        K = K1;
    }
    free(lo); free(hi);
}

/* ---- walk mode ---- */
static u64 TOP, KMAX, ROOTNB; static _Atomic u64 NEXT; static u64 NCHK; static u64 CHK[24];
static _Atomic u64 COUNT[24];              /* open seats <= CHK[j] */
static void *walk_worker(void *arg) {
    (void)arg;
    uint32_t *lo = malloc(L * 4), *hi = malloc(L * 4);
    u64 *loc = calloc(NCHK, 8);
    for (;;) {
        u64 K0 = atomic_fetch_add(&NEXT, L);
        if (K0 > KMAX) break;
        u64 n = (K0 + L > KMAX + 1) ? KMAX + 1 - K0 : L, maxs = 6 * (K0 + n - 1) + 1, nb = 0;
        u64 a = 0, b = ROOTNB; while (a < b) { u64 m = (a + b) / 2; if (B[m] * B[m] <= maxs) a = m + 1; else b = m; } nb = a;
        close_walls(K0, n, nb, lo, hi, 1);
        memset(loc, 0, NCHK * 8);            /* loc[j]: open seats in (CHK[j-1], CHK[j]] */
        u64 j = 0;
        for (u64 i = 0; i < n; i++) {
            u64 s1 = 6 * (K0 + i) - 1, s2 = s1 + 2;
            while (j < NCHK && s1 > CHK[j]) j++;
            if (j == NCHK) break;
            if (!lo[i]) loc[j]++;
            if (!hi[i]) { u64 jj = j; while (jj < NCHK && s2 > CHK[jj]) jj++; if (jj < NCHK) loc[jj]++; }
        }
        for (u64 q = 0; q < NCHK; q++) atomic_fetch_add(&COUNT[q], loc[q]);
    }
    free(lo); free(hi); free(loc); return NULL;
}

/* ---- edge mode: two separate Miller-Rabin base sets ---- */
static u64 mulm(u64 a, u64 b, u64 m) { return (u64)((u128)a * b % m); }
static u64 powm(u64 a, u64 e, u64 m) { u64 r = 1; a %= m; while (e) { if (e & 1) r = mulm(r, a, m); a = mulm(a, a, m); e >>= 1; } return r; }
static int mr(u64 n, const u64 *bs, int nb) {
    u64 d = n - 1; int s = 0; while (!(d & 1)) { d >>= 1; s++; }
    for (int i = 0; i < nb; i++) {
        u64 a = bs[i] % n; if (!a) continue;
        u64 x = powm(a, d, n); if (x == 1 || x == n - 1) continue;
        int ok = 0; for (int j = 1; j < s; j++) { x = mulm(x, x, n); if (x == n - 1) { ok = 1; break; } }
        if (!ok) return 0;
    }
    return 1;
}
static const u64 BASE_A[12] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37};
static const u64 BASE_B[7] = {2, 325, 9375, 28178, 450775, 9780504, 1795265022};
static u64 E_K0, E_KEND; static _Atomic u64 E_NAMED, E_CLOSED, E_BADA, E_BADB, E_BADCERT, E_LAST, E_FIRST;
static void *edge_worker(void *arg) {
    (void)arg;
    uint32_t *lo = malloc(L * 4), *hi = malloc(L * 4);
    for (;;) {
        u64 K0 = atomic_fetch_add(&NEXT, L);
        if (K0 >= E_KEND) break;
        u64 n = (K0 + L > E_KEND) ? E_KEND - K0 : L;
        close_walls(K0, n, ROOTNB, lo, hi, 0);
        u64 named = 0, closed = 0, ba = 0, bb = 0, bc = 0, last = 0, first = ~0ull;
        for (u64 i = 0; i < n; i++) for (int f = -1; f <= 1; f += 2) {
            u64 s = 6 * (K0 + i) + f; uint32_t c = f < 0 ? lo[i] : hi[i];
            if (c) { closed++; if (s % c) bc++; }
            else { named++; if (!mr(s, BASE_A, 12)) ba++; if (!mr(s, BASE_B, 7)) bb++; if (s > last) last = s; if (s < first) first = s; }
        }
        atomic_fetch_add(&E_NAMED, named); atomic_fetch_add(&E_CLOSED, closed);
        atomic_fetch_add(&E_BADA, ba); atomic_fetch_add(&E_BADB, bb); atomic_fetch_add(&E_BADCERT, bc);
        u64 o = atomic_load(&E_LAST); while (last > o && !atomic_compare_exchange_weak(&E_LAST, &o, last));
        o = atomic_load(&E_FIRST); while (first < o && !atomic_compare_exchange_weak(&E_FIRST, &o, first));
    }
    free(lo); free(hi); return NULL;
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: walk TOP THREADS | edge SEATS THREADS\n"); return 1; }
    int T = atoi(argv[3]); double t0 = now(); pthread_t th[64];
    if (!strcmp(argv[1], "walk")) {
        TOP = (u64)strtod(argv[2], NULL); KMAX = (TOP + 1) / 6;
        u64 root = (u64)sqrtl((long double)TOP) + 2;
        walk_blocks(root + 1000); ROOTNB = NB;
        for (u64 p = 10; p < TOP; p *= 10) CHK[NCHK++] = p;
        CHK[NCHK++] = TOP;
        fprintf(stderr, "blocks from the walk: %llu (largest %llu) in %.1fs\n", (unsigned long long)NB, (unsigned long long)B[NB - 1], now() - t0);
        atomic_store(&NEXT, 1);
        for (int i = 0; i < T; i++) pthread_create(&th[i], NULL, walk_worker, NULL);
        for (int i = 0; i < T; i++) pthread_join(th[i], NULL);
        u64 run = 2;                            /* 2 and 3, the two mirrors */
        for (u64 j = 0; j < NCHK; j++) {
            run += atomic_load(&COUNT[j]);
            printf("primes <= %llu : %llu\n", (unsigned long long)CHK[j], (unsigned long long)run);
        }
        printf("walk to %llu on %d threads: %.1fs\n", (unsigned long long)TOP, T, now() - t0);
    } else {
        u64 seats = (u64)strtod(argv[2], NULL), walls = seats / 2;
        E_KEND = (u64)(UINT64_MAX / 6);         /* last wall whose right wing is below 2^64 */
        if (6 * E_KEND + 1 < 6 * E_KEND) E_KEND--;
        E_K0 = E_KEND - walls; E_KEND += 1;
        walk_blocks(4294967296ull + 1000); ROOTNB = NB;
        fprintf(stderr, "blocks from the walk: %llu (largest %llu) in %.1fs\n", (unsigned long long)NB, (unsigned long long)B[NB - 1], now() - t0);
        atomic_store(&NEXT, E_K0); atomic_store(&E_FIRST, ~0ull);
        for (int i = 0; i < T; i++) pthread_create(&th[i], NULL, edge_worker, NULL);
        for (int i = 0; i < T; i++) pthread_join(th[i], NULL);
        printf("edge of 2^64: walls %llu to %llu (%llu seats)\n", (unsigned long long)E_K0, (unsigned long long)(E_KEND - 1), (unsigned long long)(2 * (E_KEND - E_K0)));
        printf("named %llu primes, first %llu, last %llu\n", (unsigned long long)E_NAMED, (unsigned long long)E_FIRST, (unsigned long long)E_LAST);
        printf("Miller-Rabin set A disagrees on %llu, set B on %llu; closed seats %llu, without a dividing block %llu\n",
               (unsigned long long)E_BADA, (unsigned long long)E_BADB, (unsigned long long)E_CLOSED, (unsigned long long)E_BADCERT);
        printf("on %d threads: %.1fs\n", T, now() - t0);
    }
    return 0;
}
