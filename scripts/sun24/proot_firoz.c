/* Sun 1208.2683 Conj. 2.4(i),(ii): p_n(a) = n-th prime whose smallest positive primitive root is a (a > 0),
   resp. whose largest negative primitive root is a (a < 0, i.e. -1, -2, ... tried in that order).
   Claim: p_{n+1}(a) < p_n(a)^{1+1/n} for all n (a not a perfect power), except a = -2, n = 13.
   r = n log(p_{n+1}/p_n) / log p_n; report max r per a and all violations.   usage: ./proot_firoz X AMAX */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
static uint32_t *pr; static int np;
static uint64_t mulmod(uint64_t a, uint64_t b, uint64_t m) { return (unsigned __int128) a * b % m; }
static uint64_t powmod(uint64_t a, uint64_t e, uint64_t m) { uint64_t r = 1; a %= m; while(e) { if(e & 1) r = mulmod(r, a, m); a = mulmod(a, a, m); e >>= 1; } return r; }
typedef struct { uint64_t last, n; double best; uint64_t bp, bn, bg; } st_t;
int main(int argc, char **argv) {
	uint64_t X = strtoull(argv[1], 0, 10); int AM = atoi(argv[2]);
	uint32_t R = (uint32_t) sqrt((double) X) + 2;
	char *c = calloc(R + 1, 1); pr = malloc(sizeof(uint32_t) * R);
	for(uint32_t i = 2; i <= R; ++i) if(!c[i]) { pr[np++] = i; for(uint64_t j = (uint64_t) i * i; j <= R; j += i) c[j] = 1; }
	st_t *P = calloc(AM + 1, sizeof(st_t)), *N = calloc(AM + 1, sizeof(st_t));
	const uint64_t SEG = 1 << 24; char *seg = malloc(SEG); long viol = 0;
	for(uint64_t lo = 3; lo <= X; lo += SEG) {
		uint64_t hi = lo + SEG - 1; if(hi > X) hi = X;
		memset(seg, 0, hi - lo + 1);
		for(int k = 0; k < np; ++k) { uint64_t p = pr[k]; if(p * p > hi) break;
			uint64_t s = (lo + p - 1) / p * p; if(s < p * p) s = p * p; for(uint64_t j = s; j <= hi; j += p) seg[j - lo] = 1; }
		for(uint64_t p = lo; p <= hi; ++p) {
			if(seg[p - lo]) continue;
			/* distinct prime factors of p - 1 */
			uint64_t m = p - 1, f[20]; int nf = 0;
			for(int k = 0; k < np; ++k) { uint64_t q = pr[k]; if(q * q > m) break; if(m % q == 0) { f[nf++] = q; while(m % q == 0) m /= q; } }
			if(m > 1) f[nf++] = m;
			int gp = 0, gn = 0;
			for(int g = 1; g <= AM && (!gp || !gn); ++g) {
				for(int sgn = 0; sgn < 2; ++sgn) {
					if(sgn == 0 && (gp || g == 1)) continue;
					if(sgn == 1 && gn) continue;
					uint64_t gg = sgn == 0 ? (uint64_t) g % p : (p - (uint64_t) g % p) % p;
					if(gg == 0) continue;
					int ok = 1;
					for(int t = 0; t < nf && ok; ++t) if(powmod(gg, (p - 1) / f[t], p) == 1) ok = 0;
					if(ok) { if(sgn == 0) gp = g; else gn = g; }
				}
			}
			for(int sgn = 0; sgn < 2; ++sgn) {
				int a = sgn == 0 ? gp : gn; if(!a) continue;
				st_t *s = sgn == 0 ? &P[a] : &N[a];
				if(s->n >= 1 && s->last > 1) {
					double r = (double) s->n * log1p((double) (p - s->last) / (double) s->last) / log((double) s->last);
					if(r > s->best) { s->best = r; s->bp = s->last; s->bn = s->n; s->bg = p - s->last; }
					if(r >= 1) { ++viol; printf("VIOLATION a=%s%d n=%llu p_n=%llu p_n+1=%llu r=%.6f\n", sgn ? "-" : "", a, (unsigned long long) s->n, (unsigned long long) s->last, (unsigned long long) p, r); fflush(stdout); }
				}
				s->last = p; s->n++;
			}
		}
		if(((lo / SEG) & 15) == 0) fprintf(stderr, "reached %.3g violations %ld\n", (double) hi, viol);
	}
	printf("# a  count  n_at_max  p_n  gap  max_r   (X=%.3g)\n", (double) X);
	for(int a = 2; a <= AM; ++a) if(P[a].n) printf("%d %llu %llu %llu %llu %.6f\n", a, (unsigned long long) P[a].n, (unsigned long long) P[a].bn, (unsigned long long) P[a].bp, (unsigned long long) P[a].bg, P[a].best);
	for(int a = 1; a <= AM; ++a) if(N[a].n) printf("-%d %llu %llu %llu %llu %.6f\n", a, (unsigned long long) N[a].n, (unsigned long long) N[a].bn, (unsigned long long) N[a].bp, (unsigned long long) N[a].bg, N[a].best);
	printf("# total violations %ld\n", viol);
}
