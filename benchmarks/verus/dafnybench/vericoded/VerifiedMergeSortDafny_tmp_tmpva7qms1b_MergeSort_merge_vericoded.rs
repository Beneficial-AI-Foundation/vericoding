use vstd::prelude::*;

verus! {

spec fn merged(a1: Seq<int>, a2: Seq<int>, b: &Vec<int>, start: int, end: int) -> bool {
    &&& end - start == a2.len() + a1.len()
    &&& 0 <= start <= end <= b.len()
    &&& a1.to_multiset().add(a2.to_multiset()) == b@.subrange(start, end).to_multiset()
}

spec fn sorted_slice(a: &Vec<int>, start: int, end: int) -> bool {
    &&& 0 <= start <= end <= a.len()
    &&& forall|i: int, j: int| start <= i <= j < end ==> a@[i] <= a@[j]
}

spec fn sorted_seq(a: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < a.len() ==> a[i] <= a[j]
}

spec fn sorted(a: &Vec<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < a.len() ==> a@[i] <= a@[j]
}

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
fn merge(a1: Seq<int>, a2: Seq<int>, start: int, end: int, b: &mut Vec<int>)
    requires 
        sorted_seq(a1),
        sorted_seq(a2),
        end - start == a1.len() + a2.len(),
        0 <= start < end < a1.len() && end <= a2.len() < old(b).len(),
        end < a1.len() && end < a2.len(),
        old(b).len() == a2.len() + a1.len(),
    ensures 
        sorted_slice(b, start, end),
        merged(a1, a2, b, start, end),
// </vc-spec>
// <vc-code>
{
}
// </vc-code>

fn main() {}

}