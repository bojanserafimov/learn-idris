# learn-idris

My adventures in learning the [idris](https://www.idris-lang.org/) programming
language, open-sourced for the sole purpose of spreading the joy of type-driven development.

## Example 1: Proof that the square root of 2 is irrational

The file `irrational_sqrt_2.idr` defines a function `irrational_sqrt_2`, which takes
two natural numbers `x` and `y`, a proof that `y` is nonzero, and a proof that `x*x = 2*(y*y)`.
The function returns an instance of `Void`, which is a type that can't be instantiated
(it doesn't have a constructor at all).

Idris successfully compiles this code, and the totality checker confirms that this
function is defined for all inputs. Since the function can only return an impossible
construction, it follows that the inputs of the function cannot be constructed, which
means there are no such `x` and `y`.
