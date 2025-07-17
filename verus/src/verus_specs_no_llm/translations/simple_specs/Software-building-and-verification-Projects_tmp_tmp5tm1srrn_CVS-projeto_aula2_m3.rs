// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_m3(x: int, y: int) -> z: bool
    ensures
        z ==> x==y
;

proof fn lemma_m3(x: int, y: int) -> (z: bool)
    ensures
        z ==> x==y
{
    false
}

}