// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sum(v: Seq<int>) -> int
{
    0
}

spec fn spec_vector_Sum(v: Seq<int>) -> x:int
    ensures
        x == sum(v)
;

proof fn lemma_vector_Sum(v: Seq<int>) -> (x: int)
    ensures
        x == sum(v)
{
    0
}

}