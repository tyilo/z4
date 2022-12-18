# z4

[![PyPI](https://img.shields.io/pypi/v/z4-solver)](https://pypi.org/project/z4-solver/)

[z3](https://github.com/Z3Prover/z3) with some improvements:
* Change the right shift operation on `BitVec`'s to be logical instead of arithmetic
* Extend the `*` operation on `BoolRef`'s to work between two `BoolRef`'s.
* Add additional operations to `BoolRef`'s:
  * `+`, returning an Int kind such that e.g `True + True + False == 2`
  * `&`, utilizing `And()`
  * `|`, utilizing `Or()`
  * `~`, utilizing `Not()`
* Add the `ByteVec` class
* Some helper methods for solving:
  * `easy_solve`
  * `find_all_solutions`
  * `easy_prove`
* Add some helper functions for z3 variables/constants:
  * `BoolToInt`
  * `Sgn`
  * `Abs`
  * `TruncDiv`

## Usage
Install with `pip install z4-solver`.

### `easy_solve`
```python3
import z4

a, b = z4.Ints("a b")
print(z4.easy_solve([a <= 10, b <= 10, a + b == 15]))
```

Output:
```
[b = 5, a = 10]
```

### `find_all_solutions`
```python3
import z4

a, b = z4.Ints("a b")
print(*z4.find_all_solutions([a <= 10, b <= 10, a + b == 15]), sep="\n")
```

Output:
```
[b = 5, a = 10]
[b = 6, a = 9]
[b = 7, a = 8]
[b = 8, a = 7]
[b = 9, a = 6]
[b = 10, a = 5]
```

### `easy_prove`
Let's try and prove that `2 * a >= a` for all integers `a`:
```python3
import z4

a = z4.Int("a")
print(z4.easy_prove(2 * a >= a))
```

Output
```
Traceback (most recent call last):
  ...
z4.Z3CounterExample: [a = -1]
```

This isn't true so we get an exception with the counter-example `a = -1`. Of course `2 * -1 = -2` which is less than `-1`.

Let's try again with the assumption that `a` must be non-negative:
```python3
print(z4.easy_prove(z4.Implies(a >= 0, 2 * a >= a)))
```

Output:
```
True
```
