// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
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