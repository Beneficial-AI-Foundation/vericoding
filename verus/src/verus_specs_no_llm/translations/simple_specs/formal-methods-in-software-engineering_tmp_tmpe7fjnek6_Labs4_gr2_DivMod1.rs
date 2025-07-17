// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_DivMod1(a: int, b: int) -> q: int, r: int
    requires
        b > 0 && a >= 0
    ensures
        a == b*q + r && 0 <= r < b
//decreases *
;

proof fn lemma_DivMod1(a: int, b: int) -> (q: int, r: int)
    requires
        b > 0 && a >= 0
    ensures
        a == b*q + r && 0 <= r < b
//decreases *
{
    (0, 0)
}

}