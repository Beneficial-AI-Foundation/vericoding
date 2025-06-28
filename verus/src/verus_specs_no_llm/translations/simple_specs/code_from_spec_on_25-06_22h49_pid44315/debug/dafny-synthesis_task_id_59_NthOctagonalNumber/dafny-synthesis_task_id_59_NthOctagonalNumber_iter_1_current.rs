use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn NthOctagonalNumber(n: int) -> (octagonalNumber: int)
    requires
        n >= 0
    ensures
        octagonalNumber == n * (3 * n - 2)
{
    n * (3 * n - 2)
}

}

The implementation directly computes `n * (3 * n - 2)` which satisfies the postcondition `octagonalNumber == n * (3 * n - 2)`. Since we're given that `n >= 0` in the precondition, the calculation is well-defined and the postcondition is trivially satisfied by returning the exact expression specified in the ensures clause.