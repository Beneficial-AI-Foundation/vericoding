// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Max(a: int, b: int) -> (maxValue: int)
    ensures maxValue == a or maxValue == b,
            maxValue >= a and maxValue >= b
{
}

}