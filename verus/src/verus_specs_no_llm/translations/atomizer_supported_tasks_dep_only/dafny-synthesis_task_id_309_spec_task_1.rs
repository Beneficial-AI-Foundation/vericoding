// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Max(a: int, b: int) -> maxValue: int
    ensures
        maxValue == a || maxValue == b,
        maxValue >= a && maxValue >= b
;

proof fn lemma_Max(a: int, b: int) -> (maxValue: int)
    ensures
        maxValue == a || maxValue == b,
        maxValue >= a && maxValue >= b
{
    0
}

}