// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_merge_sort(input: Seq<int>) -> output:seq<int>
    ensures
        SortSpec(input, output)
;

proof fn lemma_merge_sort(input: Seq<int>) -> (output: Seq<int>)
    ensures
        SortSpec(input, output)
{
    Seq::empty()
}

}