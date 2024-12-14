# ruff: noqa: D100, D101, D102, D104, INP001, PLR2004, S101

import unittest
from fractions import Fraction

import pytest

from z4 import (
    ByteVec,
    Int,
    Real,
    Z3UnboundedError,
    Z3UnknownError,
    Z3UnsatError,
    easy_solve,
    maximize,
    minimize,
)


class Tests(unittest.TestCase):
    def test_maximize_int(self) -> None:
        a = Int("a")
        v, m = maximize(3 * a, [a * 2 <= 5])
        assert v == 6
        assert m[a].as_long() == 2

    def test_maximize_real(self) -> None:
        a = Real("a")
        v, m = maximize(3 * a, [a * 2 <= 5])
        assert v == Fraction(15, 2)
        assert m[a].as_fraction() == Fraction(5, 2)

    def test_maximize_unbounded_int(self) -> None:
        a = Int("a")
        with pytest.raises(Z3UnboundedError):
            maximize(a, [])

    def test_maximize_unbounded_real(self) -> None:
        a = Real("a")
        with pytest.raises(Z3UnboundedError):
            maximize(a, [])

    def test_maximize_no_solution(self) -> None:
        a = Int("a")
        with pytest.raises(Z3UnsatError):
            maximize(a, [2 * a > 4, 2 * a < 6])

    def test_maximize_unknown(self) -> None:
        a = Real("a")
        with pytest.raises(Z3UnknownError):
            maximize(a, [2**a == 3])

    def test_minimize_int(self) -> None:
        a = Int("a")
        v, m = minimize(3 * a, [a * 2 >= 3])
        assert v == 6
        assert m[a].as_long() == 2

    def test_minimize_real(self) -> None:
        a = Real("a")
        v, m = minimize(3 * a, [a * 2 >= 3])
        assert v == Fraction(9, 2)
        assert m[a].as_fraction() == Fraction(3, 2)

    def test_minimize_unbounded_int(self) -> None:
        a = Int("a")
        with pytest.raises(Z3UnboundedError):
            minimize(a, [])

    def test_minimize_unbounded_real(self) -> None:
        a = Real("a")
        with pytest.raises(Z3UnboundedError):
            minimize(a, [])

    def test_minimize_no_solution(self) -> None:
        a = Int("a")
        with pytest.raises(Z3UnsatError):
            minimize(a, [2 * a > 4, 2 * a < 6])

    def test_minimize_unknown(self) -> None:
        a = Real("a")
        with pytest.raises(Z3UnknownError):
            minimize(a, [2**a == 3])

    def test_rshift(self) -> None:
        a = ByteVec("a", 1)
        b = ByteVec("b", 1)
        c = ByteVec("c", 1)
        d = ByteVec("d", 1)

        m = easy_solve([a == 0xFE, b == (a >> 1), c == 0x2, d == (0xFE >> c)])
        assert b.value(m) == b"\x7f"
        assert d.value(m) == b"?"

    def test_byte_vec(self) -> None:
        text = ByteVec("text", 3)
        m = easy_solve([text[0] == ord("F"), text[1] == ord("O"), text[2] == ord("O")])
        assert text.value(m) == b"FOO"

    def test_bool_operations(self) -> None:
        x = Int("x")
        y = Int("y")

        m = easy_solve(
            [
                ((x == 4) | (x < 0))
                + (~(x == y) & (y == 4)) * (x**2 == y) * 1
                + (x == 1337) * 0
                == 2
            ]
        )
        assert m[x] == -2
        assert m[y] == 4


if __name__ == "__main__":
    unittest.main()
