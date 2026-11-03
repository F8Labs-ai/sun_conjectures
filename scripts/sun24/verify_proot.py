# Independent check of a counterexample to Sun 1208.2683 Conj. 2.4(ii) (largest negative primitive root).
# Smallest-prime-factor sieve (numpy) instead of trial division; Python pow; exact comparison with mpmath.
import sys, numpy as np
from mpmath import mp, mpf, log
P_N, P_N1, N_CLAIM, A = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])  # A = 3 for a = -3
L = P_N1 + 1
spf = np.zeros(L, dtype=np.int32)
for i in range(2, int(L**0.5) + 1):
    if spf[i] == 0:
        blk = spf[i*i::i]; blk[blk == 0] = i; spf[i*i::i] = blk
def distinct_factors(m):
    fs = []
    while m > 1:
        q = int(spf[m]) or m
        fs.append(q)
        while m % q == 0: m //= q
    return fs
def lnpr(p):  # g such that -g is the largest negative primitive root mod p
    fs = distinct_factors(p - 1)
    g = 1
    while True:
        x = (-g) % p
        if x and all(pow(x, (p - 1) // q, p) != 1 for q in fs): return g
        g += 1
primes = np.nonzero(spf[2:] == 0)[0] + 2
cnt = 0; seq_last = None; hits = []
for p in primes:
    p = int(p)
    if p < 3: continue
    if lnpr(p) == A:
        cnt += 1
        if p >= P_N: hits.append((cnt, p))
        if p > P_N1: break
print("members of the sequence a = -%d at or after p_n:" % A, hits[:3])
n, pn = hits[0]; n1, pn1 = hits[1]
assert pn == P_N and pn1 == P_N1 and n1 == n + 1, "mismatch"
print("n =", n, "(claimed", N_CLAIM, ")")
mp.dps = 60
lhs = n * log(mpf(pn1) / pn); rhs = log(mpf(pn))
print("n*log(p_{n+1}/p_n) =", lhs, "\nlog p_n            =", rhs, "\nr =", lhs / rhs)
print("p_{n+1} >= p_n^(1+1/n):", lhs >= rhs)
