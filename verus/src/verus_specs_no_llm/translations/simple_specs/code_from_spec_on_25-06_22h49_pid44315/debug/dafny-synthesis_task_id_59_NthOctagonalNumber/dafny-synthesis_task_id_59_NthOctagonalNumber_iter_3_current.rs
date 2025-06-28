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