// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn problem3(m: int, X: int) -> (r: int)
    requires X >= 0 and (2*m == 1 - X or m == X + 3)
    ensures r == X
{
}

}