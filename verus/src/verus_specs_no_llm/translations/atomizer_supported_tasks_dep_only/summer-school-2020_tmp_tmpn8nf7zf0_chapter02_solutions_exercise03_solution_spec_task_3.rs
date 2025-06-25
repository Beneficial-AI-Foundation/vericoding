// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsSorted(s: Seq<int>) -> bool {
    forall i :: 0 <= i < s.len()-1 ==> s.spec_index(i) <= s.spec_index(i+1)
}
spec fn SortSpec(input: Seq<int>, output: Seq<int>) -> bool {
    && IsSorted(output)
  && multiset(output) == multiset(input)
}

fn fast_sort(input: Seq<int>) -> (output: Seq<int>, output)
    ensures
        SortSpec(input, output)
{
    return Seq::empty();
}

}