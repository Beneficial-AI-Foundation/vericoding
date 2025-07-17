// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_CountToAndReturnN(n: int) -> r: int
    requires
        n >= 0
    ensures
        r == n
;

proof fn lemma_CountToAndReturnN(n: int) -> (r: int)
    requires
        n >= 0
    ensures
        r == n
{
    0
}

}