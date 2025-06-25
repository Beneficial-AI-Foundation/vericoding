// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn MedianOfThree(a: int, b: int, c: int) -> (median: int)
    ensures median == a | median == b .len()| median == c,
            (median >= a and median <= b) | (median >= b and median <= a) .len() (median >= a and median <= c) .len() (median >= c and median <= a) .len() (median >= b and median <= c) .len()| (median >= c and median <= b)
{
}

}