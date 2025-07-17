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

spec fn spec_DifferenceMinMax(a: Vec<int>) -> diff: int
    requires
        a.len() > 0
    ensures
        diff == Max(a.index(..)) - Min(a.index(..))
;

proof fn lemma_DifferenceMinMax(a: Vec<int>) -> (diff: int)
    requires
        a.len() > 0
    ensures
        diff == Max(a.index(..)) - Min(a.index(..))
{
    0
}

}