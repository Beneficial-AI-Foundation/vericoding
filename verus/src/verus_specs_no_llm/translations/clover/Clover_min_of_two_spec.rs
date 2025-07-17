// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Min(x: int, y: int) -> z: int
    ensures
        x<=y ==> z==x,
        x>y ==> z==y
;

proof fn lemma_Min(x: int, y: int) -> (z: int)
    ensures
        x<=y ==> z==x,
        x>y ==> z==y
{
    0
}

}