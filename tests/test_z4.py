import unittest
from fractions import Fraction

from z4 import (
    ByteVec,
    Int,
    Real,
    Z3Unknown,
    Z3Unsat,
    Z3Unbounded,
    easy_solve,
    maximize,
    minimize,
)


class Tests(unittest.TestCase):
    def test_maximize_int(self):
        a = Int("a")
        v, m = maximize(3 * a, [a * 2 <= 5])
        self.assertEqual(v, 6)
        self.assertEqual(m[a].as_long(), 2)

    def test_maximize_real(self):
        a = Real("a")
        v, m = maximize(3 * a, [a * 2 <= 5])
        self.assertEqual(v, Fraction(15, 2))
        self.assertEqual(m[a].as_fraction(), Fraction(5, 2))

    def test_maximize_unbounded_int(self):
        a = Int("a")
        with self.assertRaises(Z3Unbounded):
            maximize(a, [])

    def test_maximize_unbounded_real(self):
        a = Real("a")
        with self.assertRaises(Z3Unbounded):
            maximize(a, [])

    def test_maximize_no_solution(self):
        a = Int("a")
        with self.assertRaises(Z3Unsat):
            maximize(a, [4 < 2 * a, 2 * a < 6])

    def test_maximize_unknown(self):
        a = Real("a")
        with self.assertRaises(Z3Unknown):
            maximize(a, [2**a == 3])

    def test_minimize_int(self):
        a = Int("a")
        v, m = minimize(3 * a, [a * 2 >= 3])
        self.assertEqual(v, 6)
        self.assertEqual(m[a].as_long(), 2)

    def test_minimize_real(self):
        a = Real("a")
        v, m = minimize(3 * a, [a * 2 >= 3])
        self.assertEqual(v, Fraction(9, 2))
        self.assertEqual(m[a].as_fraction(), Fraction(3, 2))

    def test_minimize_unbounded_int(self):
        a = Int("a")
        with self.assertRaises(Z3Unbounded):
            minimize(a, [])

    def test_minimize_unbounded_real(self):
        a = Real("a")
        with self.assertRaises(Z3Unbounded):
            minimize(a, [])

    def test_minimize_no_solution(self):
        a = Int("a")
        with self.assertRaises(Z3Unsat):
            minimize(a, [4 < 2 * a, 2 * a < 6])

    def test_minimize_unknown(self):
        a = Real("a")
        with self.assertRaises(Z3Unknown):
            minimize(a, [2**a == 3])

    def test_rshift(self):
        a = ByteVec("a", 1)
        b = ByteVec("b", 1)
        c = ByteVec("c", 1)
        d = ByteVec("d", 1)

        m = easy_solve([a == 0xFE, b == (a >> 1), c == 0x2, d == (0xFE >> c)])
        self.assertEqual(b.value(m), b"\x7F")
        self.assertEqual(d.value(m), b"\x3F")

    def test_byte_vec(self):
        text = ByteVec("text", 3)
        m = easy_solve([text[0] == ord("F"), text[1] == ord("O"), text[2] == ord("O")])
        self.assertEqual(text.value(m), b"FOO")

    def test_bool_operations(self):
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
        self.assertEqual(m[x], -2)
        self.assertEqual(m[y], 4)


if __name__ == "__main__":
    unittest.main()
