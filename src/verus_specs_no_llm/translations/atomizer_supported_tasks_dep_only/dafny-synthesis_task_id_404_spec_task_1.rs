// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Min(a: int, b: int) -> (minValue: int)
    ensures minValue == a or minValue == b,
            minValue <= a and minValue <= b
{
}

}