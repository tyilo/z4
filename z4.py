from z3 import *


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
