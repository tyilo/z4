from z3 import *  # noqa


class Z3SolveException(Exception):
    pass


class Z3Unsat(Z3SolveException):
    pass


class Z3Unknown(Z3SolveException):
    pass


def easy_solve(constraints):
    solver = Solver()
    solver.add(*constraints)
    res = solver.check()
    if res == unsat:
        raise Z3Unsat
    elif res == unknown:
        raise Z3Unknown

    return solver.model()


def find_all_solutions(constraints):
    """
    >>> def normalize_result(r):
    ...     return sorted(sorted((f.name(), m[f].as_long()) for f in m) for m in r)
    >>> a, b, c = Ints("a b c")
    >>> normalize_result(find_all_solutions([0 <= a, a < 3]))
    [[('a', 0)], [('a', 1)], [('a', 2)]]
    >>> normalize_result(find_all_solutions([0 <= a, a < 2, b == 2 * a]))
    [[('a', 0), ('b', 0)], [('a', 1), ('b', 2)]]
    """
    solver = Solver()
    solver.add(*constraints)
    while True:
        res = solver.check()
        if res == unknown:
            raise Z3Unknown
        elif res == unsat:
            return

        model = solver.model()
        yield model

        solver.add(Not(And([f() == model[f] for f in model if f.arity() == 0])))


def easy_prove(claim):
    solver = Solver()
    solver.add(Not(claim))
    res = solver.check()
    if res == unknown:
        raise Z3Unknown

    return res == unsat


BitVecRef.__rshift__ = LShR
BitVecRef.__rrshift__ = lambda a, b: LShR(b, a)


BoolRef.__and__ = And
BoolRef.__rand__ = lambda a, b: a & b

BoolRef.__or__ = Or
BoolRef.__ror__ = lambda a, b: a | b

BoolRef.__xor__ = Xor
BoolRef.__rxor__ = lambda a, b: a ^ b

BoolRef.__invert__ = Not

BoolRef.__add__ = lambda a, b: BoolToInt(a) + (
    BoolToInt(b) if isinstance(b, BoolRef) else b
)
BoolRef.__radd__ = lambda a, b: a + b

_original_bool_ref_mul = BoolRef.__mul__
BoolRef.__mul__ = (
    lambda a, b: BoolToInt(a) * BoolToInt(b)
    if isinstance(b, BoolRef)
    else _original_bool_ref_mul(a, b)
)
BoolRef.__rmul__ = lambda a, b: a * b


class ByteVec(BitVecRef):
    def __init__(self, name, byte_count, ctx=None):
        self.byte_count = byte_count
        self.bv = BitVec(name, byte_count * 8, ctx)

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

        return Extract(8 * i + 7, 8 * i, self.bv)

    def value(self, model):
        v = model[self.bv].as_long()
        return v.to_bytes(self.byte_count, "little")


def BoolToInt(x):
    return If(x, 1, 0)


def Sgn(x):
    return If(x == 0, 0, If(x > 0, 1, -1))


def Abs(x):
    return If(x >= 0, x, -x)


def TruncDiv(a, b):
    """
    Truncated division, a / b rounded towards zero.

    >>> a, b, c = Ints("a b c")
    >>> easy_prove(Implies(TruncDiv(a, b) == c, Abs(b) * Abs(c) <= Abs(a)))
    True
    """
    v = Abs(a) / Abs(b)
    return Sgn(a) * Sgn(b) * v
