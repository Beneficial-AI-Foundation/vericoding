// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Max(a: int, b: int) -> c: int
    ensures
        a >= b ==> c == a,
        b >= a ==> c == b
;

proof fn lemma_Max(a: int, b: int) -> (c: int)
    ensures
        a >= b ==> c == a,
        b >= a ==> c == b
{
    0
}

}