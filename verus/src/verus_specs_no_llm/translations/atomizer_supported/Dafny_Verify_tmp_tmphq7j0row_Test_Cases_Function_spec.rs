// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Average(a: int, b: int) -> int
{
    0
}

spec fn spec_TripleConditions(x: int) -> r: int
    ensures
        r == 3 * x
;

proof fn lemma_TripleConditions(x: int) -> (r: int)
    ensures
        r == 3 * x
{
    0
}

}