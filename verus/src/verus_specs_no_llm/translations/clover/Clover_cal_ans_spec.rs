// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_CalDiv() -> x:int, y:int
    ensures
        x==191/7,
        y==191%7
;

proof fn lemma_CalDiv() -> (x: int, y: int)
    ensures
        x==191/7,
        y==191%7
{
    (0, 0)
}

}