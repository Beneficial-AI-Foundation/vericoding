// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Min(a: Seq<int>) -> int
    requires
        a.len() > 0
{
    0
}

spec fn spec_SumMinMax(a: Vec<int>) -> sum: int
    requires
        a.len() > 0
    ensures
        sum == Max(a.index(..)) + Min(a.index(..))
;

proof fn lemma_SumMinMax(a: Vec<int>) -> (sum: int)
    requires
        a.len() > 0
    ensures
        sum == Max(a.index(..)) + Min(a.index(..))
{
    0
}

}