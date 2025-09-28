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
// Helper function to find minimum element index in a range
fn find_min_index(a: &Vec<i32>, start: usize, end: usize) -> (result: usize)
    requires 
        start < end <= a.len(),
    ensures 
        start <= result < end,
        forall|i: int| #![trigger a@[i]] start <= i < end ==> a@[result as int] <= a@[i],
{
    let mut min_idx = start;
    let mut i = start + 1;
    
    while i < end
        invariant
            start <= min_idx < i <= end,
            start < i <= end,
            i <= a.len(),
            min_idx < a.len(),
            forall|j: int| #![trigger a@[j]] start <= j < i && 0 <= j < a.len() ==> a@[min_idx as int] <= a@[j],
        decreases end - i,
    {
        assert(i < a.len());
        assert(min_idx < a.len());
        if a[i] < a[min_idx] {
            min_idx = i;
        }
        i += 1;
    }
    min_idx
}

// Lemma to prove swapping preserves multiset
proof fn lemma_swap_preserves_multiset(a: Seq<i32>, b: Seq<i32>, i: nat, j: nat)
    requires
        i < a.len(),
        j < a.len(),
        a.len() == b.len(),
        forall|k: int| #![trigger a[k], b[k]] 0 <= k < a.len() && k != i && k != j ==> a[k] == b[k],
        a[i as int] == b[j as int],
        a[j as int] == b[i as int],
    ensures
        a.to_multiset() == b.to_multiset(),
{
    assert(a.to_multiset().count(a[i as int]) == b.to_multiset().count(a[i as int]));
    assert(a.to_multiset().count(a[j as int]) == b.to_multiset().count(a[j as int]));
}

// Lemma to prove that placing minimum element extends sorted region
proof fn lemma_min_extends_sorted(a: Seq<i32>, sorted_end: nat, min_idx: nat)
    requires
        sorted_end < a.len(),
        sorted_end <= min_idx < a.len(),
        ordered(a, 0, sorted_end),
        forall|i: int| #![trigger a[i]] sorted_end <= i < a.len() ==> a[min_idx as int] <= a[i],
        forall|i: int| #![trigger a[i]] 0 <= i < sorted_end ==> a[i] <= a[min_idx as int],
    ensures
        ordered(a, 0, sorted_end + 1),
{
    // Verus can prove this from the conditions
}
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &mut Vec<i32>)
    ensures sorted(old(a)@, a@)
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let mut i = 0;
    let ghost old_a = a@;
    
    while i < n
        invariant
            i <= n,
            a@.len() == old_a.len(),
            a@.len() == n,
            i <= a@.len(),
            ordered(a@, 0, i as nat),
            preserved(old_a, a@, 0, a@.len() as nat),
            forall|j: int, k: int| #![trigger a@[j], a@[k]] 0 <= j < i && i <= k < a@.len() ==> a@[j] <= a@[k],
        decreases n - i,
    {
        if i < n {
            assert(i < a.len());
            assert(i < n <= a.len());
            
            // Find minimum in remaining unsorted portion
            let min_idx = find_min_index(a, i, n);
            
            assert(i <= min_idx < n);
            assert(min_idx < a.len());
            
            // Store values before swapping to avoid borrowing conflicts
            let ghost old_a_iter = a@;
            let temp = a[i];
            let min_val = a[min_idx];
            
            // Swap minimum with current position
            a.set(i, min_val);
            a.set(min_idx, temp);
            
            // Prove multiset preservation after swap
            proof {
                lemma_swap_preserves_multiset(old_a_iter, a@, i as nat, min_idx as nat);
                assert(preserved(old_a, a@, 0, a@.len() as nat));
            }
            
            // Prove ordering is maintained/extended
            proof {
                assert(forall|j: int| #![trigger a@[j]] i < j < a@.len() ==> a@[i as int] <= a@[j]);
                assert(forall|j: int| #![trigger a@[j]] 0 <= j < i && 0 <= j < old_a_iter.len() && 0 <= min_idx < old_a_iter.len() ==> old_a_iter[j] <= old_a_iter[min_idx as int]);
                assert(forall|j: int| #![trigger a@[j]] 0 <= j < i && 0 <= j < a@.len() ==> a@[j] <= a@[i as int]);
                lemma_min_extends_sorted(a@, i as nat, i as nat);
            }
        }
        i += 1;
    }
}
// </vc-code>

fn main() {
}

}