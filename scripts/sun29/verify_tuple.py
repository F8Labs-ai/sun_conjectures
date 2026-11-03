# Independent check of a counterexample to Sun 1208.2683 Conj. 2.9 (E(x,x+4,x+6) = {}).
# numpy sieve of Eratosthenes, recount of the triples, sympy primality, 60-digit comparison.
import numpy as np, sympy
from mpmath import mp, mpf, log
QN, QN1 = 148770907, 148809247
L = QN1 + 7
s = np.ones(L + 1, dtype=bool); s[:2] = False
for i in range(2, int(L ** 0.5) + 1):
    if s[i]: s[i * i::i] = False
x = np.nonzero(s[:L - 6] & s[4:L - 2] & s[6:L])[0]
idx = np.searchsorted(x, QN)
print("q_n =", x[idx], " n =", idx + 1, " q_(n+1) =", x[idx + 1])
assert x[idx] == QN and x[idx + 1] == QN1
for q in (QN, QN1): assert all(sympy.isprime(q + h) for h in (0, 4, 6))
assert not any(all(sympy.isprime(y + h) for h in (0, 4, 6)) for y in range(QN + 1, QN1))
mp.dps = 60; n = idx + 1
lhs, rhs = n * log(mpf(QN1) / QN), log(mpf(QN))
print("n log(q_(n+1)/q_n) =", lhs, "\nlog q_n =", rhs, "\nr =", lhs / rhs, "\nviolation:", lhs > rhs)
