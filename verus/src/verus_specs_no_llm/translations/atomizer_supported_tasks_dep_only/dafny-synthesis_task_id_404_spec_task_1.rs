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

fn Min(a: int, b: int) -> (minValue: int)
    ensures
        minValue == a || minValue == b,
        minValue <= a && minValue <= b
{
    return 0;
}

}