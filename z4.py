import z3
from z3 import *


class Z3SolveException(Exception):
    pass


class Z3Unsat(Z3SolveException):
    pass


class Z3Unknown(Z3SolveException):
    pass


def easy_solve(constraints):
    solver = z3.Solver()
    solver.add(*constraints)
    res = solver.check()
    if res == z3.unsat:
        raise Z3Unsat
    elif res == z3.unknown:
        raise Z3Unknown

    return solver.model()


def find_all_solutions(constraints):
    """
    >>> def normalize_result(r):
    ...     return sorted(sorted((f.name(), m[f].as_long()) for f in m) for m in r)
    >>> a, b, c = z3.Ints("a b c")
    >>> normalize_result(find_all_solutions([0 <= a, a < 3]))
    [[('a', 0)], [('a', 1)], [('a', 2)]]
    >>> normalize_result(find_all_solutions([0 <= a, a < 2, b == 2 * a]))
    [[('a', 0), ('b', 0)], [('a', 1), ('b', 2)]]
    """
    solver = z3.Solver()
    solver.add(*constraints)
    while True:
        res = solver.check()
        if res == z3.unknown:
            raise Z3Unknown
        elif res == z3.unsat:
            return

        model = solver.model()
        yield model

        solver.add(z3.Not(z3.And([f() == model[f] for f in model if f.arity() == 0])))


def easy_prove(claim):
    solver = z3.Solver()
    solver.add(z3.Not(claim))
    res = solver.check()
    if res == z3.unknown:
        raise Z3Unknown

    return res == z3.unsat


z3.BitVecRef.__rshift__ = z3.LShR
z3.BitVecRef.__rrshift__ = lambda a, b: z3.LShR(b, a)


class ByteVec(z3.BitVecRef):
    def __init__(self, name, byte_count, ctx=None):
        self.byte_count = byte_count
        self.bv = z3.BitVec(name, byte_count * 8, ctx)

    def __getattr__(self, attr):
        return getattr(self.bv, attr)

    def __len__(self):
        return self.byte_count

    def __getitem__(self, i):
        if not isinstance(i, int):
            raise TypeError

        if i < 0:
            i += len(self)

        if not (0 <= i < len(self)):
            raise IndexError

        return z3.Extract(8 * i + 7, 8 * i, self.bv)

    def value(self, model):
        v = model[self.bv].as_long()
        return v.to_bytes(self.byte_count, "little")


def BoolToInt(x):
    return z3.If(x, 1, 0)


def Sgn(x):
    return z3.If(x == 0, 0, z3.If(x > 0, 1, -1))


def Abs(x):
    return z3.If(x >= 0, x, -x)


def TruncDiv(a, b):
    """
    Truncated division, a / b rounded towards zero.

    >>> a, b, c = z3.Ints("a b c")
    >>> easy_prove(z3.Implies(TruncDiv(a, b) == c, Abs(b) * Abs(c) <= Abs(a)))
    True
    """
    v = Abs(a) / Abs(b)
    return Sgn(a) * Sgn(b) * v


def _test():
    a = ByteVec("a", 1)
    b = ByteVec("b", 1)
    c = ByteVec("c", 1)
    d = ByteVec("d", 1)

    s = z3.Solver()
    s.add(a == 0xFE)
    s.add(b == (a >> 1))
    s.add(c == 0x2)
    s.add(d == (0xFE >> c))
    assert s.check() == z3.sat
    m = s.model()

    assert m[b].as_long() == 0x7F
    assert m[d].as_long() == 0x3F

    text = ByteVec("text", 3)
    s2 = z3.Solver()
    s2.add(text[0] == ord("F"))
    s2.add(text[1] == ord("O"))
    s2.add(text[2] == ord("O"))
    assert s2.check() == z3.sat
    assert text.value(s2.model()) == b"FOO"


if __name__ == "__main__":
    _test()
