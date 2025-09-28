use vstd::prelude::*;

verus! {

// Works by dividing the input list into two parts: sorted and unsorted. At the beginning, 
// the sorted part is empty and the unsorted part contains all the elements.

// <vc-helpers>
// Helper function to find the index of the minimum element in a range
proof fn lemma_min_element_properties(a: &Vec<i32>, start: usize, min_idx: usize)
    requires
        start < a.len(),
        start <= min_idx < a.len(),
        forall|k: int| start <= k < a.len() ==> a[min_idx as int] <= a[k],
    ensures
        a[min_idx as int] <= a[start as int],
{
}

// Helper lemma to prove that swapping two elements preserves the multiset
proof fn lemma_swap_preserves_multiset(old_seq: Seq<i32>, new_seq: Seq<i32>, i: int, j: int)
    requires
        0 <= i < old_seq.len(),
        0 <= j < old_seq.len(),
        new_seq.len() == old_seq.len(),
        new_seq[i] == old_seq[j],
        new_seq[j] == old_seq[i],
        forall|k: int| 0 <= k < old_seq.len() && k != i && k != j ==> new_seq[k] == old_seq[k],
    ensures
        new_seq.to_multiset() == old_seq.to_multiset(),
{
    // The multiset is preserved because we're just swapping two elements
    assert forall|elem: i32| #[trigger] new_seq.to_multiset().count(elem) == old_seq.to_multiset().count(elem) by {
        // Count occurrences in both sequences
        let count_new = new_seq.filter(|e: i32| e == elem).len();
        let count_old = old_seq.filter(|e: i32| e == elem).len();
        
        // The swap doesn't change the count of any element
        assert(count_new == count_old);
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
    
    for i in 0..n
        invariant
            // Array length unchanged
            a.len() == n,
            // The sorted portion [0..i) is sorted
            forall|j: int, k: int| 0 <= j < k < i ==> a[j] <= a[k],
            // All elements in sorted portion are <= all elements in unsorted portion
            forall|j: int, k: int| 0 <= j < i && i <= k < n ==> a[j] <= a[k],
            // Multiset preservation
            a@.to_multiset() == old(a)@.to_multiset(),
    {
        if i < n {
            // Find the minimum element in the unsorted portion [i..n)
            let mut min_idx = i;
            
            for j in (i + 1)..n
                invariant
                    a.len() == n,
                    i <= min_idx < n,
                    // min_idx points to the minimum element seen so far in [i..j)
                    forall|k: int| i <= k < j ==> a[min_idx as int] <= a[k],
                    // Maintain outer loop invariants
                    forall|j: int, k: int| 0 <= j < k < i ==> a[j] <= a[k],
                    forall|j: int, k: int| 0 <= j < i && i <= k < n ==> a[j] <= a[k],
                    a@.to_multiset() == old(a)@.to_multiset(),
            {
                if a[j] < a[min_idx] {
                    min_idx = j;
                }
            }
            
            // Swap the minimum element with a[i]
            if min_idx != i {
                // Read both values before mutation
                let temp_i = a[i];
                let temp_min = a[min_idx];
                
                proof {
                    let old_a_seq = a@;
                    
                    assert(a.len() == n);
                    assert(i < a.len());
                    assert(min_idx < a.len());
                }
                
                a.set(i, temp_min);
                a.set(min_idx, temp_i);
                
                proof {
                    // Prove that the swap preserves the multiset
                    let old_a_seq = old(a)@;
                    let prev_a_seq = (a@).drop_last().push(temp_i).update(i as int, temp_min);
                    lemma_swap_preserves_multiset(prev_a_seq, a@, i as int, min_idx as int);
                    assert(a@.to_multiset() == old(a)@.to_multiset());
                }
            }
        }
    }
}
// </vc-code>

fn main() {
}

}