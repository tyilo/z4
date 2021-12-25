# z4

[z3](https://github.com/Z3Prover/z3) with some improvements:
* Change the right shift operation on `BitVec`'s to be logical instead of arithmetic
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

Standard usage:

```python3
import z4

a, b = z4.Ints("a b")
print(*z4.find_all_solutions([a > 0, b > 0, a % b == 3, a > b, a + b == 19]), sep="\n")
```

Output:
```
[b = 4, a = 15, div0 = [else -> 3], mod0 = [else -> 3]]
[b = 8, a = 11, div0 = [else -> 1], mod0 = [else -> 3]]
```
