# z4

[![PyPI](https://img.shields.io/pypi/v/z4-solver)](https://pypi.org/project/z4-solver/)

[z3](https://github.com/Z3Prover/z3) with some improvements:

* `BitVec`:
  * Change the right shift operation to be logical instead of arithmetic

* Add the `ByteVec` class
* Add some helper methods for solving:
  * `easy_solve`
  * `find_all_solutions`
  * `easy_prove`

* Add some helper functions for z3 variables/constants:
  * `BoolToInt`
  * `Sgn`
  * `TruncDiv`

# Features implemented upstream

These features were first provided by z4, before z3 included these features.
They have now been removed from z4.

* `BoolRef`:
  * Support `*` for two `BoolRef`'s [`8efaaaf`](https://github.com/Z3Prover/z3/commit/8efaaaf24982ce810b8ea85fdf74eedc3dea29ad), [`ec74a87`](https://github.com/Z3Prover/z3/commit/ec74a874232b6b23b17c741a91fff75f8d2fa6c7)
  * Support `+` [`f90b10a`](https://github.com/Z3Prover/z3/commit/f90b10a0c8e7f292bbe6288452f6176d1d73e608), [`a9513c1`](https://github.com/Z3Prover/z3/commit/a9513c19989454ac4aeaa83bdb6310cf6386835d)
  * Support `&`, `|` and `~` [`f90b10a`](https://github.com/Z3Prover/z3/commit/f90b10a0c8e7f292bbe6288452f6176d1d73e608)
  * Support `^` [`764f0d5`](https://github.com/Z3Prover/z3/commit/764f0d54a436bd93069778a385517e74aea47150)

* Helper functions:
  * `Abs` [`cf08cdf`](https://github.com/Z3Prover/z3/commit/cf08cdff9c62b8db2805dbd9c4935ccb9569f08d)

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
