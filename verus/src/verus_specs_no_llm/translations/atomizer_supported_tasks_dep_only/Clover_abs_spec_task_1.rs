// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Abs(x: int) -> y: int
    ensures
        x>=0 ==> x==y,
        x<0 ==> x+y==0
;

proof fn lemma_Abs(x: int) -> (y: int)
    ensures
        x>=0 ==> x==y,
        x<0 ==> x+y==0
{
    0
}

}