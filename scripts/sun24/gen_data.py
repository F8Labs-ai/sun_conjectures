# Builds the certificate token stream for the Lean proof of the counterexample to Sun 2.4(ii).
# Members: primes p with -3 the largest negative primitive root (i.e. -3 is one, -2 and -1 are not).
# Token format (see Sunproj/PrimRoot/Checker.lean):
#   member : d w k s_1..s_k [cert(R)]     p = nxt + d, s_i = odd prime factors < 2^16 of p-1,
#                                          R = cofactor, w = 0 (p%8 in {1,3}) or a divisor w of p-1
#                                          with (-2)^((p-1)/w) = 1 mod p
#   cert(q): g k s_1..s_k [cert(R')]       Lucas certificate: g generates (Z/q)^*
import sys, pickle, numpy as np
N2 = 51460433
SMALL = 1 << 16
L = N2 + 1
spf = np.zeros(L, dtype=np.int32)
for i in range(2, int(L ** 0.5) + 1):
    if spf[i] == 0:
        blk = spf[i * i::i]; blk[blk == 0] = i; spf[i * i::i] = blk
def factors(m):
    fs = []
    while m > 1:
        q = int(spf[m]) or m
        fs.append(q)
        while m % q == 0: m //= q
    return fs
def is_pr(x, p, fs):
    return x % p != 0 and all(pow(x, (p - 1) // q, p) != 1 for q in fs)
def split(m):
    fs = factors(m)
    ss = [q for q in fs if q != 2 and q < SMALL]
    R = m
    while R % 2 == 0: R //= 2
    for s in ss:
        while R % s == 0: R //= s
    assert R == 1 or (R >= SMALL and R in fs), (m, R)
    return fs, ss, R
def cert(q):
    fs, ss, R = split(q - 1)
    g = 2
    while not is_pr(g, q, fs): g += 1
    out = [g, len(ss)] + ss
    if R > 1: out += cert(R)
    return out
if __name__ == '__main__':
    primes = np.nonzero(spf[2:] == 0)[0] + 2
    members = []
    for p in primes:
        p = int(p)
        if p < 5: continue
        fs = factors(p - 1)
        if is_pr(p - 3, p, fs) and not is_pr(p - 2, p, fs):
            members.append(p)
    print("members", len(members), "index of 51459203:", members.index(51459203) + 1, file=sys.stderr)
    toks = []  # one token list per member
    nxt = 0
    for p in members:
        fs, ss, R = split(p - 1)
        if p % 8 in (1, 3): w = 0
        else: w = next(r for r in fs if r != 2 and pow(p - 2, (p - 1) // r, p) == 1)
        t = [p - nxt, w, len(ss)] + ss
        if R > 1: t += cert(R)
        toks.append((p, t)); nxt = p + 1
    pickle.dump(toks, open(sys.argv[1], "wb"))
    print("tokens", sum(len(t) for _, t in toks), file=sys.stderr)
    