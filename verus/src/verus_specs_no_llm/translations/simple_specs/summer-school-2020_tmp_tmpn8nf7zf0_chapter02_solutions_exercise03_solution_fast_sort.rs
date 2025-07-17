// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsSorted(s: Seq<int>) -> bool {
    forall |i: int| 0 <= i < s.len()-1 ==> s.index(i) <= s.index(i+1)
}
spec fn SortSpec(input: Seq<int>, output: Seq<int>) -> bool {
    && IsSorted(output)
 && multiset(output) == multiset(input)
}

spec fn spec_fast_sort(input: Seq<int>) -> output:seq<int>)
// ensures SortSpec(input, output
    ensures
        SortSpec(input, output)
;

proof fn lemma_fast_sort(input: Seq<int>) -> (output: Seq<int>, output)
    ensures
        SortSpec(input, output)
{
    Seq::empty()
}

}