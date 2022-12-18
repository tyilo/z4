import unittest

from z4 import ByteVec, Int, easy_solve


class Tests(unittest.TestCase):
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
