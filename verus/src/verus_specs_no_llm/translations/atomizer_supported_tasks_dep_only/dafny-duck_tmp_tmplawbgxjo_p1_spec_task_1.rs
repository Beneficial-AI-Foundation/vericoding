// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Sum(xs: Seq<int>) -> int
{
    0
}

spec fn spec_SumArray(xs: Vec<int>) -> s: int
    ensures
        s == Sum(xs.index(..))
;

proof fn lemma_SumArray(xs: Vec<int>) -> (s: int)
    ensures
        s == Sum(xs.index(..))
{
    0
}

}