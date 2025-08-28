use vstd::prelude::*;

verus! {

spec fn ordered(a: Seq<int>, left: int, right: int) -> bool {
    &&& 0 <= left <= right <= a.len()
    &&& forall |i: int| #![trigger a[i]] left < i < right ==> a[i-1] <= a[i]
}

// <vc-helpers>
spec fn find_min(a: Seq<int>, start: int, end: int) -> int
    requires
        0 <= start <= end <= a.len(),
    ensures
        start <= find_min(a, start, end) < end,
        forall |k: int| start <= k < end ==> a[find_min(a, start, end)] <= a[k],
{
    let mut min_idx = start;
    let mut i = start;
    while i < end
        invariant
            start <= i <= end,
            start <= min_idx < end,
            forall |k: int| start <= k < i ==> a[min_idx] <= a[k],
    {
        if a[i] < a[min_idx] {
            min_idx = i;
        }
        i = i + 1;
    }
    min_idx
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn selection_sort(a: &mut Vec<int>)
    ensures 
        ordered(a@, 0, a.len() as int),
        a.len() == old(a).len(),
        a@.to_multiset() =~= old(a)@.to_multiset(),
// </vc-spec>
// </vc-spec>

// <vc-code>
fn selection_sort(a: &mut Vec<int>)
    ensures
        ordered(a@, 0, a.len() as int),
        a.len() == old(a).len(),
        a@.to_multiset() =~= old(a)@.to_multiset(),
{
    let n = a.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            ordered(a@, 0, i as int),
            forall |j: int, k: int| 0 <= j < i && i <= k < n ==> a[j] <= a[k],
            a@.to_multiset() =~= old(a)@.to_multiset(),
    {
        let min_idx = find_min(a@, i as int, n as int);
        if i != min_idx as usize {
            a.swap(i, min_idx as usize);
        }
        i = i + 1;
    }
}
// </vc-code>

fn main() {}

}