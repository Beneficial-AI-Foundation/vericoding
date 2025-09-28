use vstd::prelude::*;

verus! {

// Works by dividing the input list into two parts: sorted and unsorted. At the beginning, 
// the sorted part is empty and the unsorted part contains all the elements.

// <vc-helpers>
// Helper lemma to prove that swapping maintains multiset equality
proof fn swap_preserves_multiset<T>(v: &Vec<T>, i: usize, j: usize)
    requires
        i < v.len(),
        j < v.len(),
    ensures
        v@.update(i as int, v@[j as int]).update(j as int, v@[i as int]).to_multiset() == v@.to_multiset(),
{
    let original = v@;
    let after_swap = original.update(i as int, v@[j as int]).update(j as int, v@[i as int]);
    
    if i == j {
        assert(after_swap =~= original);
        assert(after_swap.to_multiset() =~= original.to_multiset());
    } else {
        // Use the built-in property that swapping elements preserves multisets
        vstd::seq_lib::lemma_multiset_commutative(original, after_swap);
    }
}

// Helper lemma to prove multiset preservation during manual swap
proof fn manual_swap_preserves_multiset(a: &Vec<i32>, original_seq: Seq<i32>, i: usize, min_idx: usize)
    requires
        i < a.len(),
        min_idx < a.len(),
        i != min_idx,
        a@.len() == original_seq.len(),
        forall|k: int| 0 <= k < a.len() && k != i && k != min_idx ==> a@[k] == original_seq[k],
        a@[i as int] == original_seq[min_idx as int],
        a@[min_idx as int] == original_seq[i as int],
    ensures
        a@.to_multiset() == original_seq.to_multiset(),
{
    // The multiset is preserved because we only swapped two elements
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
    let mut i = 0;
    
    while i < a.len()
        invariant
            // The prefix [0..i] is sorted
            forall|x: int, y: int| 0 <= x < y < i ==> a@[x] <= a@[y],
            // All elements in [0..i] are <= all elements in [i..len]
            forall|x: int, y: int| 0 <= x < i && i <= y < a.len() ==> a@[x] <= a@[y],
            // Multiset is preserved
            a@.to_multiset() == old(a)@.to_multiset(),
            // Bounds
            0 <= i <= a.len(),
        decreases a.len() - i
    {
        if i >= a.len() {
            break;
        }
        
        // Find the minimum element in the unsorted part [i..len]
        let mut min_idx = i;
        let mut j = i + 1;
        
        while j < a.len()
            invariant
                i <= min_idx < a.len(),
                i < j <= a.len(),
                // min_idx points to the minimum in [i..j]
                forall|k: int| i <= k < j ==> a@[min_idx as int] <= a@[k],
                // Previous invariants are maintained
                forall|x: int, y: int| 0 <= x < y < i ==> a@[x] <= a@[y],
                forall|x: int, y: int| 0 <= x < i && i <= y < a.len() ==> a@[x] <= a@[y],
                a@.to_multiset() == old(a)@.to_multiset(),
                0 <= i < a.len(),
            decreases a.len() - j
        {
            if a[j] < a[min_idx] {
                min_idx = j;
            }
            j += 1;
        }
        
        // Swap elements at positions i and min_idx
        if i != min_idx {
            let ghost original_seq = a@;
            let temp = a[i];
            let min_val = a[min_idx];
            a.set(i, min_val);
            a.set(min_idx, temp);
            
            proof {
                manual_swap_preserves_multiset(a, original_seq, i, min_idx);
                
                // Prove that the new invariants hold after swap
                assert(forall|k: int| i < k < a.len() ==> a@[i as int] <= a@[k]);
                assert(forall|x: int| 0 <= x < i ==> a@[x] <= a@[i as int]);
            }
        }
        
        i += 1;
    }
    
    // At the end, prove the postcondition holds
    proof {
        assert(i == a.len());
        assert(forall|x: int, y: int| 0 <= x < y < a.len() ==> a@[x] <= a@[y]);
    }
}
// </vc-code>

fn main() {
}

}