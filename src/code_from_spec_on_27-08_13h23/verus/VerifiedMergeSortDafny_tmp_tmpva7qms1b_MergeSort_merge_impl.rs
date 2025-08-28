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
proof fn lemma_multiset_add_comm(a: Seq<int>, b: Seq<int>)
    ensures
        a.to_multiset().add(b.to_multiset()) == b.to_multiset().add(a.to_multiset())
{
}

proof fn lemma_subrange_multiset(a: Vec<int>, start: int, end: int, i: int, val: int)
    requires
        0 <= start <= i < end <= a.len(),
    ensures
        a@.subrange(start, end).to_multiset().add(singleton_multiset(val)) == 
        a@.subrange(start, i).to_multiset().add(singleton_multiset(val)).add(a@.subrange(i, end).to_multiset())
{
}

proof fn lemma_sorted_subrange(a: Vec<int>, start: int, end: int, i: int)
    requires
        0 <= start <= i < end <= a.len(),
        sorted_slice(&a, start, end),
    ensures
        sorted_slice(&a, start, i),
        sorted_slice(&a, i, end),
{
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
fn merge(a1: Seq<int>, a2: Seq<int>, start: int, end: int, b: &mut Vec<int>)
    requires 
        sorted_seq(a1),
        sorted_seq(a2),
        end - start == a1.len() + a2.len(),
        0 <= start <= end <= b.len(),
        b.len() == old(b).len(),
    ensures 
        sorted_slice(b, start, end),
        merged(a1, a2, b, start, end),
{
    let mut i: int = 0;
    let mut j: int = 0;
    let mut k: int = start;

    while k < end
        invariant
            0 <= i <= a1.len(),
            0 <= j <= a2.len(),
            start <= k <= end,
            i + j == k - start,
            sorted_slice(b, start, k),
            merged(a1.subrange(0, i), a2.subrange(0, j), b, start, k),
    {
        if i < a1.len() && (j >= a2.len() || a1[i] <= a2[j]) {
            b.set(k as usize, a1[i]);
            i = i + 1;
        } else {
            b.set(k as usize, a2[j]);
            j = j + 1;
        }
        k = k + 1;
    }
}
// </vc-code>

fn main() {}

}