// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Min(a: int, b: int) -> minValue: int
    ensures
        minValue == a || minValue == b,
        minValue <= a && minValue <= b
;

proof fn lemma_Min(a: int, b: int) -> (minValue: int)
    ensures
        minValue == a || minValue == b,
        minValue <= a && minValue <= b
{
    0
}

}