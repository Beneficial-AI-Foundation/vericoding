// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Max(a: int, b: int) -> (maxValue: int)
    ensures
        maxValue == a || maxValue == b,
        maxValue >= a && maxValue >= b
{
    if a >= b {
        a
    } else {
        b
    }
}

}