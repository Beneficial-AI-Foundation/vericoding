// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn Sorted(q: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < q.len() ==> q[i] <= q[j]
}

fn MergeSort(a: Vec<int>) -> (b: Vec<int>)
    ensures b.len() == a.len() and Sorted(b[..]) and multiset(a[..]) == multiset(b[..])
{
}

}