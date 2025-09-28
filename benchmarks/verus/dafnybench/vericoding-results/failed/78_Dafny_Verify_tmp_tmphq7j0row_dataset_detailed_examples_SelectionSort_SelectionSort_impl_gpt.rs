use vstd::prelude::*;

verus! {

// Works by dividing the input list into two parts: sorted and unsorted. At the beginning, 
// the sorted part is empty and the unsorted part contains all the elements.

// <vc-helpers>
use vstd::prelude::*;

verus! {

pub open spec fn sorted_range(s: Seq<i32>, lo: int, hi: int) -> bool {
    forall|i: int, j: int| lo <= i < j < hi ==> #[trigger] s[i] <= #[trigger] s[j]
}

pub open spec fn prefix_leq_suffix(s: Seq<i32>, k: int, n: int) -> bool {
    forall|p: int, q: int| 0 <= p < k <= q < n ==> #[trigger] s[p] <= #[trigger] s[q]
}

proof fn swap_seq_preserves_multiset<T>(s: Seq<T>, i: int, j: int)
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
    ensures
        s.update(i, s[j]).update(j, s[i]).to_multiset() == s.to_multiset(),
{
    // Rely on the definition of to_multiset over sequences, which is insensitive to element order.
}

}
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &mut Vec<i32>)
    ensures
        // Ensures the final array is sorted in ascending order
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
        // Ensures that the final array has the same elements as the initial array
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let mut i: usize = 0;

    // Outer loop over the boundary between sorted prefix [0, i) and unsorted suffix [i, n)
    while i < n
        invariant
            a.len() == n,
            0 <= i <= n,
            // The prefix [0, i) is sorted
            sorted_range(a@, 0, i as int),
            // Every element in the prefix is <= every element in the suffix [i, n)
            prefix_leq_suffix(a@, i as int, n as int),
            // Multiset of elements preserved from the start
            a@.to_multiset() == old(a)@.to_multiset(),
    {
        // Find the index of the minimum element in the suffix [i, n)
        let mut min_idx: usize = i;
        let mut j: usize = i + 1;
        while j < n
            invariant
                a.len() == n,
                i <= min_idx,
                min_idx < j,
                j <= n,
                // min_idx is always within [i, j)
                i <= min_idx < j,
                // a[min_idx] is the minimum over the current scanned range [i, j)
                forall|k: int| i as int <= k < j as int ==> #[trigger] a@[min_idx as int] <= #[trigger] a@[k],
        {
            if a[j] < a[min_idx] {
                // Prove new minimality when updating min_idx := j
                proof {
                    // For any k in [i, j), since previously a@[min_idx]
// </vc-code>

fn main() {
}

}