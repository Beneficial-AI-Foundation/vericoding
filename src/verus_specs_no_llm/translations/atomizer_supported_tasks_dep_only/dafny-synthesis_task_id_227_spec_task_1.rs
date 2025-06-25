// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn MinOfThree(a: int, b: int, c: int) -> (min: int)
    ensures min <= a and min <= b and min <= c,
            (min == a) | (min == b) .len()| (min == c)
{
}

}