// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn max(a: int, b: int) -> int
{
    0
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