z4
============

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
