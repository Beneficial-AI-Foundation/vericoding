// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Max(x: int, y: int) -> a:int
    ensures
        a == x || a == y,
        x > y ==> a == x,
        x <= y ==> a == y
;

proof fn lemma_Max(x: int, y: int) -> (a: int)
    ensures
        a == x || a == y,
        x > y ==> a == x,
        x <= y ==> a == y
{
    0
}

}