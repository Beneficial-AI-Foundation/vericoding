// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn merged(a1: Seq<i32>, a2: Seq<i32>, b: &Vec<i32>, start: int, end: int) -> bool {
    &&& end - start == a2.len() + a1.len()
    &&& 0 <= start <= end <= b.len()
    &&& a1.to_multiset().add(a2.to_multiset()) == b@.subrange(start, end).to_multiset()
}

spec fn sorted_slice(a: &Vec<i32>, start: int, end: int) -> bool {
    &&& 0 <= start <= end <= a.len()
    &&& forall|i: int, j: int| start <= i <= j < end ==> a@[i] <= a@[j]
}

spec fn sorted_seq(a: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < a.len() ==> a[i] <= a[j]
}

spec fn sorted(a: &Vec<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < a.len() ==> a@[i] <= a@[j]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn mergeSimple(a1: Seq<i32>, a2: Seq<i32>, start: usize, end: usize, b: &mut Vec<i32>)
    requires
        sorted_seq(a1),
        sorted_seq(a2),
        0 <= start <= end <= old(b).len(),
        a1.len() + a2.len() == end - start + 1,
    ensures
        sorted_slice(b, start as int, end as int),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}