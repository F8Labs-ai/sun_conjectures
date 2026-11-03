# Builds the Lean certificate for the counterexample to Sun 2.9 (E(x, x+4, x+6) = {}):
#   q_n = 148770907, q_{n+1} = 148809247, n = 77055.
# Writes Sunproj/Triple/Data/Tnnn.lean (members 1 .. 77055), Sunproj/Triple/Gap.lean and
# Sunproj/Triple/Sun29.lean.
# Token format (see Sunproj/Triple/Checker.lean):
#   member : d cert(x) cert(x+4) cert(x+6)     x = nxt + d
#   cert(q): g k s_1..s_k [cert(R)]            Lucas certificate (PrimRoot.certPrime)
#   gap    : d                                 2 <= d < x, d divides x, x+4 or x+6
import sys, os, math, numpy as np
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../Sunproj/Triple')
QN, QN1, NIDX = 148770907, 148809247, 77055
SMALL = 1 << 16
CH = 750           # members per chunk
GCH = 10000        # gap integers per chunk
L = QN1 + 7
spf = np.zeros(L + 1, dtype=np.int32)
for i in range(2, int(L ** 0.5) + 1):
    if spf[i] == 0:
        blk = spf[i * i::i]; blk[blk == 0] = i; spf[i * i::i] = blk
isp = spf == 0; isp[:2] = False
def factors(m):
    fs = []
    while m > 1:
        q = int(spf[m]) or m
        fs.append(q)
        while m % q == 0: m //= q
    return fs
def is_gen(g, p, fs):
    return g % p != 0 and all(pow(g, (p - 1) // q, p) != 1 for q in fs)
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
    while not is_gen(g, q, fs): g += 1
    out = [g, len(ss)] + ss
    if R > 1: out += cert(R)
    return out

# --- Python model of the Lean checker (Checker.lean), run on the generated data ---
def small_prime(s): return s < SMALL and s >= 2 and all(s % t for t in range(2, math.isqrt(s) + 1))
SPc = {}
def sp(s):
    if s not in SPc: SPc[s] = small_prime(s)
    return SPc[s]
def cofactor(m, ss): return m // math.gcd(m, (2 * math.prod(ss)) ** 32)
def lucas_ok(q, g, ss, R):
    return (3 <= q and (q - 1) % 2 == 0 and pow(g, (q - 1) // 2, q) == q - 1 and
            all(pow(g, (q - 1) // s, q) != 1 for s in ss) and (R == 1 or pow(g, (q - 1) // R, q) != 1))
def cert_prime(f, q, l, i):
    if f == 0 or i + 2 > len(l): return None
    g, k = l[i], l[i + 1]; ss = l[i + 2:i + 2 + k]; j = i + 2 + k
    R = cofactor(q - 1, ss)
    if not (all(sp(s) for s in ss) and lucas_ok(q, g, ss, R)): return None
    return j if R == 1 else cert_prime(f - 1, R, l, j)
def sim_run(nxt, l):
    i, cnt = 0, 0
    while i < len(l):
        x = nxt + l[i]; j = i + 1
        for h in (0, 4, 6):
            j = cert_prime(32, x + h, l, j)
            if j is None: return None
        nxt, cnt, i = x + 1, cnt + 1, j
    return nxt, cnt
def sim_gap(nxt, l):
    for d in l:
        if not (2 <= d < nxt and (nxt % d == 0 or (nxt + 4) % d == 0 or (nxt + 6) % d == 0)): return None
        nxt += 1
    return nxt

if __name__ == '__main__':
    xs = np.nonzero(isp[:L - 6] & isp[4:L - 2] & isp[6:L])[0]
    assert xs[NIDX - 1] == QN and xs[NIDX] == QN1, (xs[NIDX - 1], xs[NIDX])
    members = [int(x) for x in xs[:NIDX + 1]]
    toks, nxt = [], 0
    for x in members:
        t = [x - nxt] + cert(x) + cert(x + 4) + cert(x + 6)
        toks.append((x, t)); nxt = x + 1
    print('members', NIDX, 'tokens', sum(len(t) for _, t in toks[:NIDX]), file=sys.stderr)
    gap = []
    for x in range(QN + 1, QN1):
        ds = [int(spf[x + h]) for h in (0, 4, 6) if spf[x + h] != 0]
        assert ds, x
        gap.append(min(ds))
    assert sim_gap(QN + 1, gap) == QN1
    lit = lambda flat: ',\n  '.join(', '.join(map(str, flat[i:i + 16])) for i in range(0, len(flat), 16))
    HDR = 'set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\n'
    import os; os.makedirs(OUT + '/Data', exist_ok=True)
    names = []
    for c, a in enumerate(range(0, NIDX, CH)):
        b = min(a + CH, NIDX)
        lo = 0 if a == 0 else toks[a - 1][0] + 1
        hi = toks[b - 1][0] + 1
        flat = [v for _, t in toks[a:b] for v in t]
        assert sim_run(lo, flat) == (hi, b - a), c
        nm = 'T%03d' % c; names.append((nm, lo, hi, b))
        open(f'{OUT}/Data/{nm}.lean', 'w').write(f'''import Sunproj.Triple.Checker

/-! Certificates for the members {a + 1}–{b} of the sequence `x` with `x, x + 4, x + 6` prime
(generated). -/

namespace Triple

{HDR}/-- Certificate tokens. -/
def D{nm} : List ℕ := [
  {lit(flat)}]

{HDR}lemma D{nm}_ok : run {b - a} {lo} 0 D{nm} = some ({hi}, {b - a}) := by decide +kernel

lemma D{nm}_count : Nat.count IsT {lo} + {b - a} ≤ Nat.count IsT {hi} := run_sound0 D{nm}_ok

end Triple
''')
    print(len(names), 'member chunks', file=sys.stderr)
    # gap: several definitions in one file
    gparts = []
    for c, a in enumerate(range(0, len(gap), GCH)):
        b = min(a + GCH, len(gap))
        gparts.append((c, QN + 1 + a, QN + 1 + b, gap[a:b]))
    body = ''
    for c, lo, hi, g in gparts:
        assert sim_gap(lo, g) == hi
        body += f'''{HDR}/-- Non-membership certificates for `{lo} … {hi - 1}`. -/
def gap{c} : List ℕ := [
  {lit(g)}]

{HDR}lemma gap{c}_ok : runGap {hi - lo} {lo} gap{c} = some {hi} := by decide +kernel

'''
    chainG = ' |>.trans '.join(f'(runGap_sound _ _ _ _ gap{c}_ok)' for c, _, _, _ in reversed(gparts))
    t1 = toks[NIDX - 1][1][:]; t1[0] = 0
    t2 = toks[NIDX][1][:]; t2[0] = 0
    assert sim_run(QN, t1) == (QN + 1, 1) and sim_run(QN1, t2) == (QN1 + 1, 1)
    open(f'{OUT}/Gap.lean', 'w').write(f'''import Sunproj.Triple.Checker

/-! `q_n = {QN}` and `q_(n+1) = {QN1}` are members, and nothing in between is (generated). -/

namespace Triple

{body}lemma gap_count : Nat.count IsT {QN1} = Nat.count IsT {QN + 1} :=
  {chainG}

lemma qn_ok : run 1 {QN} 0 {t1} = some ({QN + 1}, 1) := by decide +kernel

lemma qn1_ok : run 1 {QN1} 0 {t2} = some ({QN1 + 1}, 1) := by decide +kernel

end Triple
''')
    print('gap tokens', len(gap), 'in', len(gparts), 'parts', file=sys.stderr)
    imports = '\n'.join(f'import Sunproj.Triple.Data.{nm}' for nm, _, _, _ in names)
    steps, prev = [], '(Nat.zero_le _)'
    for i, (nm, lo, hi, b) in enumerate(names):
        steps.append(f'  have h{i} : {b} ≤ Nat.count IsT {hi} := chain {prev} D{nm}_count rfl')
        prev = f'h{i}'
    steps = '\n'.join(steps)
    assert names[-1][2] == QN + 1
    open(f'{OUT}/Count.lean', 'w').write(f'''{imports}

/-! Chains the member chunks (generated). -/

namespace Triple

lemma chain {{a b lo hi c : ℕ}} (ha : a ≤ Nat.count IsT lo)
    (h : Nat.count IsT lo + c ≤ Nat.count IsT hi) (hb : b = a + c) : b ≤ Nat.count IsT hi := by
  omega

/-- At least {NIDX} members are `≤ {QN}`. -/
theorem count_le : {NIDX} ≤ Nat.count IsT {QN + 1} := by
{steps}
  exact {prev}

end Triple
''')
    print('done', file=sys.stderr)
