// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn merge_sort(input: Seq<int>) -> (output: Seq<int>)
    ensures SortSpec(input, output)
{
}

}