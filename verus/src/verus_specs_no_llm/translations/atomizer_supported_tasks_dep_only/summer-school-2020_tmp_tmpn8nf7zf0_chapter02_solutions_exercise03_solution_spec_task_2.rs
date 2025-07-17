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

spec fn spec_merge(a: Seq<int>, b: Seq<int>) -> output:seq<int>
    requires
        IsSorted(a),
        IsSorted(b)
//
    ensures
        IsSorted(output),
        SortSpec(a+b, output)
  //decreases a.len()+b.len()
;

proof fn lemma_merge(a: Seq<int>, b: Seq<int>) -> (output: Seq<int>)
    requires
        IsSorted(a),
        IsSorted(b)
//
    ensures
        IsSorted(output),
        SortSpec(a+b, output)
  //decreases a.len()+b.len()
{
    Seq::empty()
}

}