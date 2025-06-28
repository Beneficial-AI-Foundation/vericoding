use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SwapSimultaneous(X: int, Y: int) -> (x: int, y: int)
    ensures
        x == Y,
        y == X,
{
    (Y, X)
}

}

The code you provided is actually correct. The function `SwapSimultaneous` takes two integers `X` and `Y` as input and returns them swapped as `(x, y)` where `x` gets the value of `Y` and `y` gets the value of `X`. The ensures clauses correctly specify this swap behavior, and the implementation `(Y, X)` correctly satisfies these postconditions.

If you're still getting verification errors, it might be due to:

Here's an alternative version with explicit proof annotations if needed:

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SwapSimultaneous(X: int, Y: int) -> (x: int, y: int)
    ensures
        x == Y,
        y == X,
{
    let result = (Y, X);
    proof {
        assert(result.0 == Y);
        assert(result.1 == X);
    }
    result
}

}

However, the original implementation should work fine as Verus can automatically verify that `(Y, X)` satisfies the postconditions `x == Y` and `y == X`.