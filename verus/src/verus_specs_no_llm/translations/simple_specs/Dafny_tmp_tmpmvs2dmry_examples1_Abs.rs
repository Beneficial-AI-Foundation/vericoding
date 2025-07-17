// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn abs(x: int) -> int
{
    0
}

spec fn spec_Abs(x: int) -> y:int
    ensures
        y>=0,
        x>=0 ==> x == y,
        x<0 ==> -x == y,
        y == abs(x)
;

proof fn lemma_Abs(x: int) -> (y: int)
    ensures
        y>=0,
        x>=0 ==> x == y,
        x<0 ==> -x == y,
        y == abs(x)
{
    0
}

}