// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn MinOfThree(a: int, b: int, c: int) -> (min: int)
    ensures
        min <= a && min <= b && min <= c,
        (min == a) | (min == b) .len()| (min == c)
{
    return 0;
}

}