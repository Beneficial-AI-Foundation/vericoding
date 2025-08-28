use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper function to find the index of the minimum element in a range
spec fn min_index(v: Seq<i32>, start: int, end: int) -> int
    decreases end - start
{
    if start >= end {
        start
    } else {
        let mid = start + (end - start) / 2;
        let left_min = min_index(v, start, mid);
        let right_min = min_index(v, mid, end);
        if v[left_min] <= v[right_min] {
            left_min
        } else {
            right_min
        }
    }
}

// Helper spec to check if a prefix of the sequence is sorted
spec fn is_sorted_prefix(v: Seq<i32>, up_to: int) -> bool {
    forall|i: int, j: int| 0 <= i < j < up_to ==> v[i] <= v[j]
}

// Helper spec to check if all elements from a certain index are greater or equal to a value
spec fn all_greater_equal(v: Seq<i32>, start: int, value: i32) -> bool {
    forall|i: int| start <= i < v.len() ==> v[i] >= value
}

// Lemma to prove properties about swapping elements
proof fn lemma_swap_preserves_multiset(v: Vec<i32>, i: int, j: int)
    requires
        0 <= i < v.len(),
        0 <= j < v.len(),
    ensures
        v@.to_multiset() == v@.swap(i as nat, j as nat).to_multiset(),
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn selection_sort(a: &mut Vec<i32>)
    ensures
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// </vc-spec>

// <vc-code>
fn selection_sort(a: &mut Vec<i32>)
    ensures
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
        a@.to_multiset() == old(a)@.to_multiset(),
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            is_sorted_prefix(a@, i as int),
            forall|k: int| 0 <= k < i ==> all_greater_equal(a@, i as int, a[k]),
            a@.to_multiset() == old(a)@.to_multiset(),
    {
        let mut min_idx: usize = i;
        let mut j: usize = i + 1;
        while j < a.len()
            invariant
                i < a.len(),
                0 <= j <= a.len(),
                0 <= min_idx < a.len(),
                forall|k: int| i <= k < j ==> a[min_idx as int] <= a[k],
                a@.to_multiset() == old(a)@.to_multiset(),
        {
            if a[j] < a[min_idx] {
                min_idx = j;
            }
            j = j + 1;
        }
        if min_idx != i {
            let ghost old_a = a@;
            a.swap(i, min_idx);
            proof {
                lemma_swap_preserves_multiset(*a, i as int, min_idx as int);
            }
        }
        i = i + 1;
    }
}
// </vc-code>

fn main() {}

}