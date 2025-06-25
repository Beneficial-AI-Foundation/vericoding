// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn peasantMult(a: int, b: int) -> (r: int)
    requires b > 0
    ensures r == a * b
{
}

}