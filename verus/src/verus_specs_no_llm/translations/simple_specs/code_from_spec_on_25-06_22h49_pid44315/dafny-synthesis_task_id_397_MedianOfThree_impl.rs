use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn MedianOfThree(a: int, b: int, c: int) -> (median: int)
    ensures
        median == a || median == b || median == c,
        (median >= a && median <= b) || (median >= b && median <= a) || 
        (median >= a && median <= c) || (median >= c && median <= a) || 
        (median >= b && median <= c) || (median >= c && median <= b)
{
    if (a <= b && b <= c) || (c <= b && b <= a) {
        b
    } else if (b <= a && a <= c) || (c <= a && a <= b) {
        a
    } else {
        c
    }
}

}