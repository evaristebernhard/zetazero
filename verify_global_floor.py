from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F


def q(x: str | int) -> F:
    return F(x)


@dataclass(frozen=True)
class I:
    lo: F
    hi: F

    @staticmethod
    def point(x: F | int) -> "I":
        y = F(x)
        return I(y, y)

    def __add__(self, other: "I" | F | int) -> "I":
        o = other if isinstance(other, I) else I.point(other)
        return I(self.lo + o.lo, self.hi + o.hi)

    __radd__ = __add__

    def __neg__(self) -> "I":
        return I(-self.hi, -self.lo)

    def __sub__(self, other: "I" | F | int) -> "I":
        o = other if isinstance(other, I) else I.point(other)
        return self + (-o)

    def __rsub__(self, other: "I" | F | int) -> "I":
        o = other if isinstance(other, I) else I.point(other)
        return o - self

    def __mul__(self, other: "I" | F | int) -> "I":
        o = other if isinstance(other, I) else I.point(other)
        vals = (
            self.lo * o.lo,
            self.lo * o.hi,
            self.hi * o.lo,
            self.hi * o.hi,
        )
        return I(min(vals), max(vals))

    __rmul__ = __mul__

    def __truediv__(self, other: F | int) -> "I":
        o = F(other)
        assert o > 0
        return I(self.lo / o, self.hi / o)

    def square(self) -> "I":
        if self.lo >= 0:
            return I(self.lo * self.lo, self.hi * self.hi)
        if self.hi <= 0:
            return I(self.hi * self.hi, self.lo * self.lo)
        return I(F(0), max(self.lo * self.lo, self.hi * self.hi))


def exp_bounds(x: F, m: int = 64) -> I:
    """Rigorous rational Taylor bounds for exp(x), 0 <= x <= 4."""
    assert 0 <= x <= 4
    term = F(1)
    partial = F(1)
    for j in range(1, m + 1):
        term *= x / j
        partial += term
    next_term = term * x / (m + 1)
    ratio = x / (m + 2)
    assert ratio < 1
    tail_upper = next_term / (1 - ratio)
    return I(partial, partial + tail_upper)


E2 = exp_bounds(F(2))


def e2_cosh_sinh(r: I) -> tuple[I, I]:
    eplus = I(exp_bounds(2 + 2 * r.lo).lo, exp_bounds(2 + 2 * r.hi).hi)
    eminus = I(exp_bounds(2 - 2 * r.hi).lo, exp_bounds(2 - 2 * r.lo).hi)
    return (eplus + eminus) / 2, (eplus - eminus) / 2


def Gprime(r: I) -> I:
    C, S = e2_cosh_sinh(r)
    r2 = r.square()
    r3 = r2 * r
    poly = (-F(14, 3)) * r3 + 8 * r2 - 4 * r + F(1, 2)
    return (
        poly
        + ((r - 1) / 2) * C
        + (r2 / 2 - r + F(3, 4)) * S
        + (F(1, 2) - r) * E2
    )


def g(r: I) -> I:
    C, S = e2_cosh_sinh(r)
    r2 = r.square()
    return (
        -14 * r2
        + 16 * r
        - 4
        + (4 * (r - 1) * S + (2 * r2 - 4 * r + 4) * C - 2 * E2) / 2
    )


def gprime(r: I) -> I:
    C, S = e2_cosh_sinh(r)
    r2 = r.square()
    return -28 * r + 16 + (2 * r2 - 4 * r + 6) * S + 6 * (r - 1) * C


def pt(s: str) -> I:
    return I.point(q(s))


def assert_gt(iv: I, bound: str) -> None:
    b = q(bound)
    assert iv.lo > b, (iv, ">", b)


def assert_lt(iv: I, bound: str) -> None:
    b = q(bound)
    assert iv.hi < b, (iv, "<", b)


def main() -> None:
    assert_gt(g(pt("0.16")), "0.025")
    assert_lt(g(pt("0.1625")), "-0.010")
    assert_lt(g(pt("0.6145")), "-0.0004")
    assert_gt(g(pt("0.6146")), "0.0012")
    assert_lt(gprime(pt("0.39")), "-0.41")
    assert_gt(gprime(pt("0.40")), "0.19")
    assert_gt(gprime(pt("0.3854")), "-0.70")
    assert_gt(gprime(pt("0.5")), "6.8")

    h_3144 = g(pt("0.3144")) + g(pt("0.6856"))
    h_3145 = g(pt("0.3145")) + g(pt("0.6855"))
    assert_gt(h_3144, "0.0019")
    assert_lt(h_3145, "-0.0010")

    gp1 = Gprime(pt("1"))

    aL, aR = q("0.16"), q("0.1625")
    gp_aL, gp_aR = Gprime(I.point(aL)), Gprime(I.point(aR))
    g_aL, g_aR = g(I.point(aL)), g(I.point(aR))
    a_width = aR - aL
    gpa_lo = max(gp_aL.lo, gp_aR.lo)
    gpa_hi = min(
        gp_aL.hi + a_width * g_aL.hi,
        gp_aR.hi + a_width * (-g_aR.lo),
    )
    gpa = I(gpa_lo, gpa_hi)

    bL, bR = q("0.6145"), q("0.6146")
    gp_bL, gp_bR = Gprime(I.point(bL)), Gprime(I.point(bR))
    g_bL, g_bR = g(I.point(bL)), g(I.point(bR))
    b_width = bR - bL
    gpb_lo = max(
        gp_bL.lo + b_width * g_bL.lo,
        gp_bR.lo - b_width * g_bR.hi,
    )
    gpb_hi = min(gp_bL.hi, gp_bR.hi)
    gpb = I(gpb_lo, gpb_hi)

    gpx = Gprime(pt("0.3144"))
    gp1mx = Gprime(pt("0.6855"))

    assert_gt(gp1, "2.8385")
    assert_lt(gp1, "2.8386")
    assert_gt(gpa, "0.7440")
    assert_lt(gpa, "0.7442")
    assert_gt(gpb, "0.2361")
    assert_lt(gpb, "0.2364")
    assert_lt(gpx, "0.6142")
    assert_gt(gp1mx, "0.2846")

    A_upper = gp1.hi - F(1, 2) + 2 * gpa.hi - 2 * gpb.lo
    D_upper = gp1.hi - gp1mx.lo - 2 * gpa.lo + F(1, 2) + gpx.hi
    M_upper = A_upper + D_upper
    cusp_lower = 2 * gp1.lo

    assert A_upper < q("3.3548"), A_upper
    assert D_upper < q("2.1802"), D_upper
    assert M_upper < q("5.535"), M_upper
    assert cusp_lower > q("5.677"), cusp_lower
    assert cusp_lower - M_upper > q("0.142"), cusp_lower - M_upper

    print("global model floor rational Taylor certificate: PASS")
    print("M upper <", float(M_upper))
    print("cusp lower >", float(cusp_lower))
    print("margin >", float(cusp_lower - M_upper))


if __name__ == "__main__":
    main()
