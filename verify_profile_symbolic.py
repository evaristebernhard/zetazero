from __future__ import annotations

from fractions import Fraction as F

# Exact formal ring Q[E2^{±1}, X^{±1}, r], where X represents exp(2r)
# and E2 represents exp(2).  A monomial key is (e2_power, x_power, r_power).
Expr = dict[tuple[int, int, int], F]


def norm(a: Expr) -> Expr:
    return {k: v for k, v in a.items() if v}


def mono(c: F | int, ep: int = 0, xp: int = 0, rp: int = 0) -> Expr:
    c = F(c)
    return {} if not c else {(ep, xp, rp): c}


def add(a: Expr, b: Expr) -> Expr:
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, F(0)) + v
    return norm(out)


def neg(a: Expr) -> Expr:
    return {k: -v for k, v in a.items()}


def sub(a: Expr, b: Expr) -> Expr:
    return add(a, neg(b))


def scale(a: Expr, c: F | int) -> Expr:
    c = F(c)
    return norm({k: c * v for k, v in a.items()})


def mul(a: Expr, b: Expr) -> Expr:
    out: Expr = {}
    for (e1, x1, r1), c1 in a.items():
        for (e2, x2, r2), c2 in b.items():
            k = (e1 + e2, x1 + x2, r1 + r2)
            out[k] = out.get(k, F(0)) + c1 * c2
    return norm(out)


def deriv(a: Expr) -> Expr:
    # d/dr X^x = 2x X^x; E2 is constant with respect to r.
    out: Expr = {}
    for (ep, xp, rp), c in a.items():
        if rp:
            k = (ep, xp, rp - 1)
            out[k] = out.get(k, F(0)) + c * rp
        if xp:
            k = (ep, xp, rp)
            out[k] = out.get(k, F(0)) + c * 2 * xp
    return norm(out)


def series_add(a: list[Expr], b: list[Expr]) -> list[Expr]:
    return [add(a[i], b[i]) for i in range(3)]


def series_scale(a: list[Expr], c: F | int) -> list[Expr]:
    return [scale(x, c) for x in a]


def series_mul(a: list[Expr], b: list[Expr]) -> list[Expr]:
    out = [{}, {}, {}]
    for i in range(3):
        for j in range(3 - i):
            out[i + j] = add(out[i + j], mul(a[i], b[j]))
    return out


ONE = mono(1)
R = mono(1, rp=1)
E2 = mono(1, ep=1)
X = mono(1, xp=1)
Xi = mono(1, xp=-1)


def rpow(n: int) -> Expr:
    return mono(1, rp=n)


# exp(p) through p^2.
EXP_P = [ONE, ONE, mono(F(1, 2))]


# E_r(a p) = integral_0^r exp(-a p t) dt.
def E_ap(a: int) -> list[Expr]:
    return [
        rpow(1),
        scale(rpow(2), F(-a, 2)),
        scale(rpow(3), F(a * a, 6)),
    ]


# E_r(c+p)=(1-exp(-(c+p)r))/(c+p), c=±2.
def E_shift(c: int) -> list[Expr]:
    xc = Xi if c == 2 else X
    numerator = [
        sub(ONE, xc),
        mul(xc, R),
        scale(mul(xc, rpow(2)), F(-1, 2)),
    ]
    reciprocal = [
        mono(F(1, c)),
        mono(F(-1, c * c)),
        mono(F(1, c * c * c)),
    ]
    return series_mul(numerator, reciprocal)


# Build the source profile exactly through p^2.
base = series_add(E_ap(2), series_scale(series_mul(E_ap(1), E_ap(1)), -2))
translated = series_scale(series_mul(E_shift(2), E_shift(-2)), 1)
translated = [mul(E2, x) for x in translated]
SOURCE = series_mul(EXP_P, series_add(base, translated))
G_source = SOURCE[2]


# Closed form used in main.tex.  sinh(r)^2=(X+X^{-1}-2)/4.
sinh_sq = scale(add(add(X, Xi), mono(-2)), F(1, 4))
poly = add(add(add(scale(rpow(4), -14), scale(rpow(3), 32)), scale(rpow(2), -24)), scale(rpow(1), 6))
coef = add(add(scale(rpow(2), 6), scale(rpow(1), -12)), mono(9))
exp_part = sub(mul(coef, sinh_sq), scale(rpow(2), 3))
G_closed = scale(add(poly, mul(E2, exp_part)), F(1, 12))

assert norm(sub(G_source, G_closed)) == {}, (G_source, G_closed)


# First derivative formula used by verify_global_floor.py.
C = scale(mul(E2, add(X, Xi)), F(1, 2))
S = scale(mul(E2, sub(X, Xi)), F(1, 2))
Gp_formula = add(
    add(
        add(
            add(scale(rpow(3), F(-14, 3)), scale(rpow(2), 8)),
            scale(rpow(1), -4),
        ),
        mono(F(1, 2)),
    ),
    add(
        mul(scale(add(R, mono(-1)), F(1, 2)), C),
        add(
            mul(add(add(scale(rpow(2), F(1, 2)), scale(R, -1)), mono(F(3, 4))), S),
            mul(add(mono(F(1, 2)), scale(R, -1)), E2),
        ),
    ),
)
assert norm(sub(deriv(G_closed), Gp_formula)) == {}


# Second derivative formula used in main.tex / verify_global_floor.py.
g_formula = add(
    add(add(scale(rpow(2), -14), scale(R, 16)), mono(-4)),
    scale(
        add(
            add(
                scale(mul(add(R, mono(-1)), S), 4),
                mul(add(add(scale(rpow(2), 2), scale(R, -4)), mono(4)), C),
            ),
            scale(E2, -2),
        ),
        F(1, 2),
    ),
)
assert norm(sub(deriv(deriv(G_closed)), g_formula)) == {}


# Cusp formula at r=1.  Substitute r=1 and X=E2.
def eval_r1(a: Expr) -> dict[int, F]:
    out: dict[int, F] = {}
    for (ep, xp, _rp), c in a.items():
        power = ep + xp
        out[power] = out.get(power, F(0)) + c
    return {k: v for k, v in out.items() if v}


cusp = scale(deriv(G_closed), 2)
# (-2 + 3 E2 (sinh 2 - 2))/6 = (-2 + 3/2(E2^2-1)-6E2)/6.
cusp_expected = {
    0: F(-7, 12),
    1: F(-1, 1),
    2: F(1, 4),
}
assert eval_r1(cusp) == cusp_expected, (eval_r1(cusp), cusp_expected)

print("source profile exact formal certificate: PASS")
