// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_simple(y: int) -> x: int
    requires
        y==6
    ensures
        x==7
;

proof fn lemma_simple(y: int) -> (x: int)
    requires
        y==6
    ensures
        x==7
{
    0
}

}