use vstd::prelude::*;

verus! {

pub fn mergeSimple(a1: Seq<int>, a2: Seq<int>, start: int, end: int, b: &mut Vec<int>)
    requires(sorted_seq(a1))
    requires(sorted_seq(a2))
    requires(0 <= start <= end <= b.len())
    requires(a1.len() + a2.len() == end - start + 1)
    ensures(sorted_slice(b, start, end))
{
}

spec fn sorted_slice(a: &Vec<int>, start: int, end: int) -> bool
    recommends(0 <= start <= end <= a.len())
{
    forall|i: int, j: int| start <= i <= j < end ==> a[i] <= a[j]
}

spec fn sorted_seq(a: Seq<int>) -> bool
{
    forall|i: int, j: int| 0 <= i <= j < a.len() ==> a[i] <= a[j]
}

}