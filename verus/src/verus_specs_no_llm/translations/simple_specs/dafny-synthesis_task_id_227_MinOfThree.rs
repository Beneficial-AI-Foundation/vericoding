// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_MinOfThree(a: int, b: int, c: int) -> min: int
    ensures
        min <= a && min <= b && min <= c,
        (min == a) | (min == b) .len()| (min == c)
;

proof fn lemma_MinOfThree(a: int, b: int, c: int) -> (min: int)
    ensures
        min <= a && min <= b && min <= c,
        (min == a) | (min == b) .len()| (min == c)
{
    0
}

}