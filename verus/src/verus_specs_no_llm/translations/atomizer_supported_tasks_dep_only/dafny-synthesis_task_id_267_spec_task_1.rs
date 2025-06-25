// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
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