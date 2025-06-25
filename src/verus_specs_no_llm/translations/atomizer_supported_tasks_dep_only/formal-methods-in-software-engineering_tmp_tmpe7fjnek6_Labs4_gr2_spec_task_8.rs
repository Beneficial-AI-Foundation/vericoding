// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn DivMod1(a: int, b: int) -> q: int, r: int
    requires b > 0 and a >= 0
    ensures a == b*q + r and 0 <= r < b
//decreases *
{
}

}