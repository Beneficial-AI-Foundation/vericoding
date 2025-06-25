// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn mult(a: int, b: int) -> (x: int)
    requires a >= 0 and b >= 0
    ensures x == a * b
{
}

}