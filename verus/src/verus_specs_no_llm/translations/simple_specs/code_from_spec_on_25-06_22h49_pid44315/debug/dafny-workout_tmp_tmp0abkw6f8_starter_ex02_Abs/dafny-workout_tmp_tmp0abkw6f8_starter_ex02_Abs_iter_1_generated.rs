- Input: `x: int` where `x < 0` (from requires clause)
- Output: `y: int` where `0 < y` and `y == -x` (from ensures clause)

Since the precondition guarantees `x < 0`, the absolute value is simply `-x`, which will be positive.

Here's the verified implementation:

// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Abs(x: int) -> (y: int)
    requires
        x < 0
    ensures
        0 < y,
        y == -x
{
    return -x;
}

}

The implementation is straightforward:
- Since `x < 0` (from the precondition), `-x` will be positive, satisfying `0 < y`
- The result `-x` directly satisfies `y == -x`
- Verus can automatically verify that both postconditions are met given the precondition