// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn NthDecagonalNumber(n: int) -> (decagonal: int)
    requires n >= 0
    ensures decagonal == 4 * n * n - 3 * n
{
}

}