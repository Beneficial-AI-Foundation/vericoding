// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Sqare(a: int) -> x:int
    requires
        a>=1
    ensures
        x == a*a
;

proof fn lemma_Sqare(a: int) -> (x: int)
    requires
        a>=1
    ensures
        x == a*a
{
    0
}

}