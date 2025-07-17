// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_peasantMult(a: int, b: int) -> r: int
    requires
        b > 0
    ensures
        r == a * b
;

proof fn lemma_peasantMult(a: int, b: int) -> (r: int)
    requires
        b > 0
    ensures
        r == a * b
{
    0
}

}