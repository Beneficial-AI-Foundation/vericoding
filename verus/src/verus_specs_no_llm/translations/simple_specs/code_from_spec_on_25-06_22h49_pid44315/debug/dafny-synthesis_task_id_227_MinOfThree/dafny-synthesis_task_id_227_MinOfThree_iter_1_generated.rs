// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn MinOfThree(a: int, b: int, c: int) -> (min: int)
    ensures
        min <= a && min <= b && min <= c,
        (min == a) || (min == b) || (min == c)
{
    if a <= b && a <= c {
        a
    } else if b <= c {
        b
    } else {
        c
    }
}

}