// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Triple1(x: int) -> r: int
    ensures
        r == 3 * x
;

proof fn lemma_Triple1(x: int) -> (r: int)
    ensures
        r == 3 * x
{
    0
}

}