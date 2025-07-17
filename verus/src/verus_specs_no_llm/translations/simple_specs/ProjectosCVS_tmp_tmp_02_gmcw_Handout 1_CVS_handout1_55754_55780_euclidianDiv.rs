// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_euclidianDiv(a: int, b: int) -> q: int,r: int
    requires
        a >= 0,
        b > 0
    ensures
        a == b * q + r
;

proof fn lemma_euclidianDiv(a: int, b: int) -> (q: int, r: int)
    requires
        a >= 0,
        b > 0
    ensures
        a == b * q + r
{
    (0, 0)
}

}