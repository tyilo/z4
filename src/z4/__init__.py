"""z3 with some improvements."""

from z3 import *  # noqa: F403, I001


from collections.abc import Iterable, Callable
from typing import Any
from z3 import (
    Abs,
    And,
    ArithRef,
    BitVec,
    BitVecRef,
    BoolRef,
    Context,
    ExprRef,
    Extract,
    If,
    LShR,
    ModelRef,
    Not,
    Optimize,
    sat,
    Solver,
    unknown,
    unsat,
)


class Z3SolveError(Exception):
    """A Z3 error."""


class Z3UnsatError(Z3SolveError):
    """Z3 has proven that the constraints cannot be satisfied."""


class Z3UnknownError(Z3SolveError):
    """Z3 doesn't know whether the constraints can be satisfied."""


class Z3CounterExampleError(Z3SolveError):
    """A counterexample to the theorem was found."""

    model: ModelRef

    def __init__(self, model: ModelRef) -> None:
        """Initialize from a model containing the counterexample."""
        super().__init__(model)
        self.model = model


class Z3UnboundedError(Z3SolveError):
    """The objective function is unbounded."""

    model: ModelRef

    def __init__(self, model: ModelRef) -> None:
        """Initialize from a feasible model."""
        super().__init__(model)
        self.model = model


def easy_solve(constraints: Iterable[BoolRef]) -> ModelRef:
    """
    Try to find a model satisfying the constraints.

    :raises Z3UnsatError: if the constraints can't be satisfied
    :raises Z3UnknownError: if Z3 can't determine whether the constraints
                            can be satisfied
    """
    solver = Solver()
    solver.add(*constraints)
    res = solver.check()
    if res == unsat:
        raise Z3UnsatError
    if res == unknown:
        raise Z3UnknownError

    return solver.model()


def find_all_solutions(constraints: Iterable[BoolRef]) -> Iterable[ModelRef]:
    """
    Find all models satisfying the constraints.

    :raises Z3UnknownError: if Z3 can't determine whether the constraints
                            can be satisfied

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
            raise Z3UnknownError
        elif res == unsat:
            return

        model = solver.model()
        yield model

        solver.add(Not(And([f() == model[f] for f in model if f.arity() == 0])))


def easy_prove(claim: BoolRef) -> bool:
    """
    Prove a claim.

    :return Always True
    :raises Z3UnknownError: if Z3 can't determine whether the claim
                            is true or not
    :raises Z3CounterExamplError: if Z3 found a counterexample to the claim
    """
    solver = Solver()
    solver.add(Not(claim))
    res = solver.check()
    if res == unknown:
        raise Z3UnknownError
    if res == sat:
        raise Z3CounterExampleError(solver.model())

    return True


def _optimize(
    cost: ArithRef,
    constraints: Iterable[BoolRef],
    dir_f: Callable[[Optimize, ArithRef], ExprRef],
    obj_f: Callable[[Optimize, ExprRef], ArithRef],
) -> tuple[ArithRef, ModelRef]:
    opt = Optimize()
    opt.add(*constraints)
    objective = dir_f(opt, cost)
    res = opt.check()
    if res == unsat:
        raise Z3UnsatError
    if res == unknown:
        raise Z3UnknownError

    model = opt.model()
    value = obj_f(opt, objective)
    if type(value) is ArithRef and str(value) in {"oo", "-1*oo"}:
        raise Z3UnboundedError(model)

    return value, model


def maximize(
    cost: ArithRef, constraints: Iterable[BoolRef]
) -> tuple[ArithRef, ModelRef]:
    """
    Maximize :cost while satisfying :constraints.

    :return (max_value, model)
    :raises Z3UnsatError: if the constraints can't be satisfied
    :raises Z3UnknownError: if Z3 can't determine whether the constraints
                            can be satisfied
    """
    return _optimize(
        cost,
        constraints,
        Optimize.maximize,
        Optimize.upper,
    )


def minimize(
    cost: ArithRef, constraints: Iterable[BoolRef]
) -> tuple[ArithRef, ModelRef]:
    """
    Minimize :cost while satisfying :constraints.

    :return (min_value, model)
    :raises Z3UnsatError: if the constraints can't be satisfied
    :raises Z3UnknownError: if Z3 can't determine whether the constraints
                            can be satisfied
    """
    return _optimize(
        cost,
        constraints,
        Optimize.minimize,
        Optimize.lower,
    )


BitVecRef.__rshift__ = LShR
BitVecRef.__rrshift__ = lambda a, b: LShR(b, a)


class ByteVec(BitVecRef):
    """Byte-vector representation of a Z3 bit-vector."""

    def __init__(self, name: str, byte_count: int, ctx: Context | None = None) -> None:
        """Create a new byte-vector with name and number of bytes."""
        self.byte_count = byte_count
        self.bv = BitVec(name, byte_count * 8, ctx)

    def __getattr__(self, attr: str) -> Any:  # noqa: ANN401
        """Get the attribute of the underlying BitVecRef."""
        return getattr(self.bv, attr)

    def __len__(self) -> int:
        """Byte count."""
        return self.byte_count

    def __getitem__(self, i: Any) -> BitVecRef:  # noqa: ANN401
        """
        I'th byte as a BitVecRef.

        Supports negative indices for indexing from the back.
        """
        if not isinstance(i, int):
            raise TypeError

        if i < 0:
            i += len(self)

        if not (0 <= i < len(self)):
            raise IndexError

        return Extract(8 * i + 7, 8 * i, self.bv)

    def value(self, model: ModelRef) -> None:
        """Byte value of this in the given model."""
        v = model[self.bv].as_long()
        return v.to_bytes(self.byte_count, "little")


def BoolToInt(x: BoolRef) -> ArithRef:  # noqa: N802
    """Map a Z3 bool to an int."""
    return If(x, 1, 0)


def Sgn(x: ArithRef) -> ArithRef:  # noqa: N802
    """Sign of x."""
    return If(x == 0, 0, If(x > 0, 1, -1))


def TruncDiv(a: ArithRef, b: ArithRef) -> ArithRef:  # noqa: N802
    """
    Calculate a / b rounded towards zero.

    >>> a, b, c = Ints("a b c")
    >>> easy_prove(Implies(TruncDiv(a, b) == c, Abs(b) * Abs(c) <= Abs(a)))
    True
    """
    v = Abs(a) / Abs(b)
    return Sgn(a) * Sgn(b) * v
