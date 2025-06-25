// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

fn Max(a: int, b: int) -> (maxValue: int)
    ensures
        maxValue == a || maxValue == b,
        maxValue >= a && maxValue >= b
{
    return 0;
}

}