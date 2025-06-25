// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn IsSorted(s: Seq<int>) -> bool {
    forall|p: int, q  0<=p<q<.len()s|: int| s[p]<=s[q]
}

fn InsertionSort(s: Seq<int>) -> (r: Seq<int>)
    ensures multiset(r) == multiset(s);,
            IsSorted(r);
{
}

}