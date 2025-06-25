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

fn MedianOfThree(a: int, b: int, c: int) -> (median: int)
    ensures
        median == a | median == b .len()| median == c,
        (median >= a && median <= b) | (median >= b && median <= a) .len() (median >= a && median <= c) .len() (median >= c && median <= a) .len() (median >= b && median <= c) .len()| (median >= c && median <= b)
{
    return 0;
}

}