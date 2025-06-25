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

fn MinOfThree(a: int, b: int, c: int) -> (min: int)
    ensures
        min <= a && min <= b && min <= c,
        (min == a) | (min == b) .len()| (min == c)
{
    return 0;
}

}