// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_m4(x: int, y: int) -> z: bool
    ensures
        z ==> x==y && x==y ==> z
;

proof fn lemma_m4(x: int, y: int) -> (z: bool)
    ensures
        z ==> x==y && x==y ==> z
{
    false
}

}