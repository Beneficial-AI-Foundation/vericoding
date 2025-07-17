// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_MedianLength(a: int, b: int) -> median: int
    requires
        a > 0 && b > 0
    ensures
        median == (a + b) / 2
;

proof fn lemma_MedianLength(a: int, b: int) -> (median: int)
    requires
        a > 0 && b > 0
    ensures
        median == (a + b) / 2
{
    0
}

}