"""Verification of the constants in the note "Integer multiplication below n log n:
the exponent kappa = 2^-74".  All conditions and margins use exact integer/Fraction
arithmetic; floating-point logarithms are used only for display and for the scan of
T*(h) over h.  Run: python3 verify_kappa.py"""
from fractions import Fraction as F
from math import comb, log, log2

def bit_net(h):          # Section 3.1 of [OAI], bit construction, ground set [h]
    v = comb(h, 3); N = v**3; m = h**3; I = 3*v*v
    W = 2*N + I*(v*3*comb(h-3, 2) + h); L = I*h*h
    return dict(v=v, N=N, m=m, W=W, L=L, s=W*m - N + 2*L)
def cx_net(h):           # Section 3.1 of [OAI], complex construction
    v = comb(h, 3); N = v**3; m = h**3; I = 3*v*v
    W = 2*N + I*(v*(comb(h-3, 3) + 3*(h-3)) + h + 1); L = I*(h+1)*h
    return dict(v=v, N=N, m=m, W=W, L=L, s=W*m - 2*N + 2*L)
def eta(d): return F(d['W']*d['m'] - d['s'], d['W']*d['m'])
def Tstar(d):            # 1 - log_m(s/W) = -ln(1-eta)/ln m  (floating point, for display)
    e = eta(d); return -log(1 - e.numerator/e.denominator)/log(d['m']) if e > 0 else float('nan')

# --- the paper's printed values (h = 100) -------------------------------------------------
b100, c100 = bit_net(100), cx_net(100)
assert (b100['W'], b100['s']) == (177176569091445000000, 177176569088785861287000000)
assert (c100['W'], c100['s']) == (1873807244643542670000, 1873807244636671267308000000)
assert eta(b100) == F(339, 22587335000000) and eta(c100) == F(73, 19906842167500)

# --- the h = 46 bit network ---------------------------------------------------------------
b = bit_net(46)
assert (b['v'], b['N'], b['m']) == (15180, 3497963832000, 97336)
assert (b['W'], b['L'], b['s']) == (28434979789999200, 1462784875200, 2767747192266968049600)
assert F(b['L'], b['N']) == F(23, 55) and eta(b) == F(9, 43518487588)
print("h=46: W_b m =", b['W']*b['m'], "  eta_b =", eta(b), " T* = %.5f * 2^-36" % (Tstar(b)*2**36))

# exponent certificates:  T ln m < eta  ==>  m^(1-T) > m(1 - T ln m) > m(1-eta) = s/W
ln2_up = F(6932, 10000); assert log(2) < 0.6932
def cert(T, d, ln_m_up): return T*ln_m_up < eta(d)
assert b['m'] < 2**17 and cert(F(6, 5)/2**36, b, 17*ln2_up)          # tau = 1-(6/5)2^-36
assert cert(F(1, 2**36), b, 17*ln2_up)                                # tau = 1-2^-36
assert b100['m'] < 2**20 and cert(F(1, 2**40), b100, 20*ln2_up)       # h=100: tau = 1-2^-40
assert cert(F(1, 2**50), c100, 20*ln2_up)                             # sigma = 1-2^-50 (paper)

# optimality of h = 46 among the bit networks (deficit N - 2L > 0 needs h >= 39)
assert all(bit_net(h)['N'] <= 2*bit_net(h)['L'] for h in range(7, 39))
best = max(range(39, 2001), key=lambda h: Tstar(bit_net(h)))
assert best == 46
print("T*(h) for h = 39..52, 100:", {h: round(Tstar(bit_net(h))*2**36, 4) for h in list(range(39, 53)) + [100]})

# guard width: s_c <= m^5 (C1 = 5) and the chain-variation route m + 6h <= m^(1+2^-10)
assert 2 <= c100['s'] <= c100['m']**5 and (1 + 600/10**6)**1024 <= 10**6

# --- parameter sets ------------------------------------------------------------------------
def check(name, T, S, beta, c, lam, lamp, C1, eps, delta, a5, kappa, axis_linear=True):
    tau, sig = 1 - T, 1 - S
    eps_max = F(1, 12) if a5 == F(3, 2) else F(1, 3)   # (40) of [OAI] / gamma = o(b) with the new alpha
    conds = [max(tau, sig) < lam < 1, tau*(1 + c/beta) < lam, max(lam, sig + beta*(1 - sig)) < lamp < 1,
             eps*C1 < 1, 0 < delta < F(1, 8), 0 < c, 0 < beta < 1, eps < eps_max]
    g = [1 - eps*(1 + c), eps*c*T, eps*(1 - lamp),
         T*(1 - eps) if axis_linear else 1 - tau - eps*(2 - tau),
         F(1, 4) - delta - a5*eps, 1 - delta - eps, eps]
    assert all(conds), name
    assert all(x > 0 for x in g) and kappa < min(g), name
    print(f"{name:7s} min g = 2^{log2(float(min(g))):.4f}  (g2 = {g[1]*2**72} * 2^-72),  kappa = 2^{log2(float(kappa)):.0f}")
    return min(g)
check("paper", F(1, 2**50), F(1, 2**50), F(1, 2), F(1, 2**56), 1 - F(1, 2**52), 1 - F(1, 2**54),
      20, F(1, 2**75), F(1, 16), F(3, 2), F(1, 2**182), axis_linear=False)
beta, lam, lamp, S = 1 - F(1, 2**10), 1 - F(1, 2**51), 1 - F(1, 2**61), F(1, 2**50)
check("step1", F(1, 2**50), S, beta, F(31, 32)/2**50, 1 - F(1, 2**56), lamp, 14, F(1, 15), F(1, 16), F(3, 2), F(1, 2**104))
check("step2", F(1, 2**40), S, beta, F(31, 32)/2**40, lam, lamp, 14, F(1, 15), F(1, 16), F(3, 2), F(1, 2**84))
check("Set A", F(1, 2**36), S, beta, F(31, 32)/2**36, lam, lamp, 14, F(1, 15), F(1, 16), F(3, 2), F(1, 2**76))
gB = check("Set B", F(6, 5)/2**36, S, beta, F(7, 6)/2**36, lam, lamp, 5, F(3, 16), F(1, 128), F(5, 4), F(1, 2**74))
assert gB == F(21, 80)/2**72
TB, cB = F(6, 5)/2**36, F(7, 6)/2**36
assert (1 - TB)*(1 + cB/beta) < 1 - F(1, 2**41)

# --- smaller Gaussian width: gamma = 2 d alpha^2 <= 8 sqrt(24) d^(3/2) b^(1/2) < 40 b^(25/32)
assert 64*24 < 40**2                       # 8 sqrt(24) < 40
assert 160**32 <= (2**34)**7               # b >= 2^34  ==>  40 b^(25/32) <= b/4  (i.e. b^(7/32) >= 160)

# --- the barrier: g2 < eps * T^2/(1-T) with eps < 1/5 and T < T*(46) ---------------------
Ts = Tstar(b)
print("barrier: (1/5) T*^2/(1-T*) = 2^%.3f" % log2(Ts*Ts/5/(1 - Ts)))
print("all checks passed")
