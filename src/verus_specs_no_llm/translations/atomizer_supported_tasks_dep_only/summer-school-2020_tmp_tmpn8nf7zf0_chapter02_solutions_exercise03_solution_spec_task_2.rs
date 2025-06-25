// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn IsSorted(s: Seq<int>) -> bool {
    forall|i: int| 0 <= i < s.len()-1 ==> s[i] <= s[i+1]
}
spec fn SortSpec(input: Seq<int>, output: Seq<int>) -> bool {
    and IsSorted(output)
  and multiset(output) == multiset(input)
}

fn merge(a: Seq<int>, b: Seq<int>) -> (output: Seq<int>)
    requires IsSorted(a),
             IsSorted(b)
//
    ensures IsSorted(output),
            SortSpec(a+b, output)
  //decreases a.len()+b.len()
{
}

}