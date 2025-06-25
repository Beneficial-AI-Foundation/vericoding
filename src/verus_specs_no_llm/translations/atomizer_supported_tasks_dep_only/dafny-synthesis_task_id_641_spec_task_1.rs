// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn NthNonagonalNumber(n: int) -> (number: int)
    requires n >= 0
    ensures number == n * (7 * n - 5) / 2
{
}

}