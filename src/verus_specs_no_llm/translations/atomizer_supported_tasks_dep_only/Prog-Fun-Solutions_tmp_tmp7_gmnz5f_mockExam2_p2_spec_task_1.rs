// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn problem2(p: int, q: int, X: int, Y: int) -> r: int, s: int
    requires p == 2*X + Y and q == X + 3
    ensures r == X and s == Y
{
}

}