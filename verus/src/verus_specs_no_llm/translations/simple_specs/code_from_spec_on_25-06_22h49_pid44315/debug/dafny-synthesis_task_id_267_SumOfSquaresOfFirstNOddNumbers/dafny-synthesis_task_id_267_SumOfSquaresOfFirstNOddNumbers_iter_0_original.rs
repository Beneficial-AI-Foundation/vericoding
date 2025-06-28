// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SumOfSquaresOfFirstNOddNumbers(n: int) -> (sum: int)
    requires
        n >= 0
    ensures
        sum == (n * (2 * n - 1) * (2 * n + 1)) / 3
{
    return 0;
}

}