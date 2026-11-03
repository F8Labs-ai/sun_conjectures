/* Sun 1208.2683 Conj. 2.8-2.10: q_1 < q_2 < ... are the x with all of f_1(x),...,f_k(x) prime. E(f) = set of n with
   q_n^{1/n} > q_{n+1}^{1/(n+1)} failing (i.e. r = n log(q_{n+1}/q_n)/log q_n >= 1).  Sun's claims:
   E(x,x+2) = {}, E(x,x+2,x+6) = E(x,x+4,x+6) = {}, E(x,2x+1) = {3,4}, E(x,2x-1) = {2,3,6}.
   N_0: least n_0 with 2Q(n) < (n-1) q_{n+1} for all n >= n_0 (claims 4, 3, 6, 3, 3).
   usage: ./tuples_firoz X */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#define NP 5
static const char *name[NP] = {"x,x+2", "x,x+2,x+6", "x,x+4,x+6", "x,2x+1", "x,2x-1"};
static const int claimN0[NP] = {4, 3, 6, 3, 3};
typedef struct { uint64_t last, n; long double Q; double best; uint64_t bn, bq; uint64_t lastN0fail; int nexc; uint64_t exc[64]; } st_t;
int main(int argc, char **argv) {
	uint64_t X = strtoull(argv[1], 0, 10), Y = 2 * X + 8;
	uint32_t R = (uint32_t) sqrt((double) Y) + 2;
	char *c = calloc(R + 1, 1); uint32_t *pr = malloc(sizeof(uint32_t) * R); int np = 0;
	for(uint32_t i = 2; i <= R; ++i) if(!c[i]) { pr[np++] = i; for(uint64_t j = (uint64_t) i * i; j <= R; j += i) c[j] = 1; }
	const uint64_t SEG = 1 << 23; char *A = malloc(SEG + 16), *D = malloc(2 * SEG + 16);
	st_t S[NP]; memset(S, 0, sizeof S);
	for(uint64_t lo = 1; lo <= X; lo += SEG) {
		uint64_t hi = lo + SEG - 1; if(hi > X) hi = X;
		/* A[i] = 1 iff lo+i composite, for i in [0, SEG+8) ; D[j] = 1 iff (2lo-1)+j composite */
		uint64_t alo = lo, ahi = hi + 8, dlo = 2 * lo - 1, dhi = 2 * hi + 1;
		memset(A, 0, ahi - alo + 1); memset(D, 0, dhi - dlo + 1);
		for(int k = 0; k < np; ++k) {
			uint64_t p = pr[k];
			if(p * p <= ahi) { uint64_t s = (alo + p - 1) / p * p; if(s < p * p) s = p * p; for(uint64_t j = s; j <= ahi; j += p) A[j - alo] = 1; }
			if(p * p <= dhi) { uint64_t s = (dlo + p - 1) / p * p; if(s < p * p) s = p * p; for(uint64_t j = s; j <= dhi; j += p) D[j - dlo] = 1; }
		}
		if(alo == 1) A[0] = 1;
		if(dlo == 1) D[0] = 1;
		for(uint64_t x = lo; x <= hi; ++x) {
			if(A[x - alo]) continue;
			int ok[NP];
			ok[0] = !A[x + 2 - alo];
			ok[1] = !A[x + 2 - alo] && !A[x + 6 - alo];
			ok[2] = !A[x + 4 - alo] && !A[x + 6 - alo];
			ok[3] = !D[2 * x + 1 - dlo];
			ok[4] = (2 * x - 1 >= dlo) ? !D[2 * x - 1 - dlo] : 0;
			for(int t = 0; t < NP; ++t) if(ok[t]) {
				st_t *s = &S[t];
				if(s->n >= 1) {
					double r = (double) s->n * log1p((double) (x - s->last) / (double) s->last) / log((double) s->last);
					if(s->n >= 1 && s->last > 1) {
						if(r >= 1) { if(s->nexc < 64) s->exc[s->nexc] = s->n; s->nexc++; }
						else if(s->n >= 20 && r > s->best) { s->best = r; s->bn = s->n; s->bq = s->last; }
					}
					/* N0 condition at index n: 2 Q(n) < (n - 1) q_{n+1} */
					if(!(2 * s->Q < (long double) (s->n - 1) * x)) s->lastN0fail = s->n;
				}
				s->Q += x; s->last = x; s->n++;
			}
		}
		if(((lo / SEG) & 63) == 0) fprintf(stderr, "reached %.3g\n", (double) hi);
	}
	printf("X = %.3g\n", (double) X);
	for(int t = 0; t < NP; ++t) {
		st_t *s = &S[t];
		printf("(%s): count %llu  E = {", name[t], (unsigned long long) s->n);
		for(int i = 0; i < s->nexc && i < 64; ++i) printf("%s%llu", i ? "," : "", (unsigned long long) s->exc[i]);
		printf("}  max r (n>=20) = %.5f at n=%llu q=%llu ;  N0 = %llu (Sun: %d)\n", s->best, (unsigned long long) s->bn, (unsigned long long) s->bq,
		       (unsigned long long) (s->lastN0fail + 1), claimN0[t]);
	}
}
