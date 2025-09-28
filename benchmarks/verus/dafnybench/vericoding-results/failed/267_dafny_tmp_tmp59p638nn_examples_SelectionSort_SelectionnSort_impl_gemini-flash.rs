use vstd::prelude::*;

verus! {

// Two-state predicate for checking if multiset is preserved
spec fn preserved(a_old: Seq<i32>, a_new: Seq<i32>, left: nat, right: nat) -> bool
    recommends left <= right <= a_old.len() && a_old.len() == a_new.len()
{
    a_old.subrange(left as int, right as int).to_multiset() == a_new.subrange(left as int, right as int).to_multiset()
}

// Predicate for checking if array slice is ordered
spec fn ordered(a: Seq<i32>, left: nat, right: nat) -> bool
    recommends left <= right <= a.len()
{
    forall|i: int| #![trigger a[i]] left < i < right ==> a[i-1] <= a[i]
}

// Two-state predicate for sorted array
spec fn sorted(a_old: Seq<i32>, a_new: Seq<i32>) -> bool
    recommends a_old.len() == a_new.len()
{
    ordered(a_new, 0, a_new.len() as nat) && preserved(a_old, a_new, 0, a_old.len() as nat)
}

// <vc-helpers>
fn get_min_index(a: &Vec<i32>, start_index: usize, end_index: usize) -> (idx: usize)
    requires
        start_index < end_index,
        end_index <= a.len(),
    ensures
        start_index <= idx < end_index, // Ensures the returned index is within bounds
        forall|k: int| start_index <= k < end_index ==> a[idx as int] <= a[k], // Ensures a[idx] is the minimum element in the slice
{
    let mut min_idx: usize = start_index;
    let mut j: usize = start_index + 1;

    #[verifier::loop_invariant(
        start_index <= j, // j can be equal to start_index + 1
        j <= end_index,
        start_index <= min_idx,
        min_idx < j,
        forall|k: int| start_index <= k && k < j ==> a[min_idx as int] <= a[k],
    )]
    while j < end_index {
        if a[j] < a[min_idx] {
            min_idx = j;
        }
        j = j + 1;
    }
    min_idx
}
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &mut Vec<i32>)
    ensures sorted(old(a)@, a@)
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let n: usize = a.len();

    #[verifier::loop_invariant(
        0 <= i,
        i <= n,
        // The prefix a[0..i] is sorted
        ordered(a@, 0, i as nat),
        // All elements in a[0..i] are less than or equal to elements in a[i..n]
        forall|k: int, l: int| 0 <= k && (k as nat) < i && (i as nat) <= l && (l as nat) < n ==> a[k] <= a[l],
        // The multiset of elements is preserved
        preserved(old(a)@, a@, 0, n as nat),
    )]
    while i < n {
        // Find the minimum element in the unsorted part a[i..n-1]
        let min_idx: usize = get_min_index(a, i, n);

        // Swap a[i] and a[min_idx]
        if i != min_idx {
            let temp = a[i];
            a.set(i, a[min_idx]);
            a.set(min_idx, temp);
        }

        i = i + 1;
    }
}
// </vc-code>

fn main() {
}

}