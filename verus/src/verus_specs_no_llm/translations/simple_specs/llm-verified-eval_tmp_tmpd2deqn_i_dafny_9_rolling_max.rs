// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isMax(m: int, numbers: Seq<int>) -> bool
{
    false
}

spec fn spec_rolling_max(numbers: Seq<int>) -> result: seq<int>
    requires
        numbers != []
    ensures
        result.len() == numbers.len(),
        forall |i: int| 0 < i < result.len() ==> isMax(result.index(i), numbers.index(0..(i+1)))
;

proof fn lemma_rolling_max(numbers: Seq<int>) -> (result: Seq<int>)
    requires
        numbers != []
    ensures
        result.len() == numbers.len(),
        forall |i: int| 0 < i < result.len() ==> isMax(result.index(i), numbers.index(0..(i+1)))
{
    Seq::empty()
}

}