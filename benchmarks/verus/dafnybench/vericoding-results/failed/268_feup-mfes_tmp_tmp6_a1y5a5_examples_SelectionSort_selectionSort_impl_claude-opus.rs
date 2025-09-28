use vstd::prelude::*;

verus! {

/* 
* Formal verification of the selection sort algorithm with Verus.
* FEUP, MIEIC, MFES, 2020/21.
*/

// Checks if array 'a' is sorted between positions 'from' (inclusive) and 'to' (exclusive).
spec fn is_sorted(a: Seq<i32>, from: int, to: int) -> bool
    recommends 0 <= from <= to <= a.len()
{
    forall|i: int, j: int| from <= i < j < to ==> a[i] <= a[j]
}

// Sorts array 'a' using the selection sort algorithm.

// Finds the position of a minimum value in non-empty subarray 'a' between positions 
// 'from' (inclusive) and 'to' (exclusive)
fn find_min(a: &Vec<i32>, from: usize, to: usize) -> (index: usize)
    requires 
        0 <= from < to <= a.len(),
    ensures 
        from <= index < to,
        forall|k: int| from as int <= k < to as int ==> a@[k] >= a@[index as int],
{
    assume(false);
    0
}

// <vc-helpers>
// Lemma: swapping two elements preserves the multiset
proof fn swap_preserves_multiset(a: Seq<i32>, i: int, j: int)
    requires
        0 <= i < a.len(),
        0 <= j < a.len(),
    ensures
        a.update(i, a[j]).update(j, a[i]).to_multiset() == a.to_multiset(),
{
    let swapped = a.update(i, a[j]).update(j, a[i]);
    // The multiset equality holds because we're just swapping elements
    assert(swapped.to_multiset() =~= a.to_multiset());
}

// Lemma: if we have a sorted prefix and swap the minimum of the suffix into position,
// the prefix extends by one element while remaining sorted
proof fn extend_sorted_prefix(a: Seq<i32>, i: int, min_idx: int)
    requires
        0 <= i < a.len(),
        i <= min_idx < a.len(),
        is_sorted(a, 0, i),
        forall|k: int| i <= k < a.len() ==> a[k] >= a[min_idx],
        forall|j: int, k: int| 0 <= j < i && i <= k < a.len() ==> a[j] <= a[k],
    ensures
        is_sorted(a.update(i, a[min_idx]).update(min_idx, a[i]), 0, i + 1),
{
    let swapped = a.update(i, a[min_idx]).update(min_idx, a[i]);
    
    assert forall|j: int, k: int| 0 <= j < k < i + 1 implies swapped[j] <= swapped[k] by {
        if k < i {
            // Both in the already sorted part
            assert(0 <= j < k < i);
            assert(0 <= j < a.len());
            assert(0 <= k < a.len());
            assert(a[j] <= a[k]);  // from is_sorted(a, 0, i)
            assert(swapped[j] == a[j]);
            assert(swapped[k] == a[k]);
            assert(swapped[j] <= swapped[k]);
        } else {
            // k == i, so we need to show swapped[j] <= swapped[i]
            assert(k == i);
            assert(0 <= j < i);
            assert(0 <= j < a.len());
            assert(swapped[i] == a[min_idx]);
            assert(swapped[j] == a[j]);
            // a[j] is in sorted prefix, and by precondition a[j] <= a[k] for all k >= i
            // Since min_idx >= i, we have a[j] <= a[min_idx]
            assert(i <= min_idx < a.len());
            assert(a[j] <= a[min_idx]); // from precondition
            assert(swapped[j] <= swapped[i]);
        }
    }
}

// Helper lemma for the sorted prefix preservation
proof fn sorted_prefix_preserved_after_swap(a: Seq<i32>, i: int, min_idx: int)
    requires
        0 <= i < a.len(),
        i <= min_idx < a.len(),
        is_sorted(a, 0, i),
    ensures
        is_sorted(a.update(i, a[min_idx]).update(min_idx, a[i]), 0, i),
{
    let swapped = a.update(i, a[min_idx]).update(min_idx, a[i]);
    
    assert forall|j: int, k: int| 0 <= j < k < i implies swapped[j] <= swapped[k] by {
        assert(0 <= j < a.len());
        assert(0 <= k < a.len());
        assert(swapped[j] == a[j]);
        assert(swapped[k] == a[k]);
        assert(a[j] <= a[k]); // from is_sorted(a, 0, i)
        assert(swapped[j] <= swapped[k]);
    }
}
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &mut Vec<i32>)
    ensures 
        is_sorted(a@, 0, a@.len() as int),
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    
    if n == 0 {
        return;
    }
    
    let mut i: usize = 0;
    
    while i < n - 1
        invariant
            0 <= i < n,
            n == a.len(),
            is_sorted(a@, 0, i as int),
            forall|j: int, k: int| 0 <= j < i as int && i as int <= k < n as int ==> #[trigger] a@[j] <= #[trigger] a@[k],
            a@.to_multiset() == old(a)@.to_multiset(),
        decreases n - 1 - i,
    {
        assert(i < n - 1);
        assert(i < n);
        assert(n > 0);
        
        let min_idx = find_min(a, i, n);
        
        assert(i < a.len());
        assert(min_idx < a.len());
        assert(i <= min_idx < n);
        
        // Store values for swap
        let temp = a[i];
        let min_val = a[min_idx];
        
        proof {
            swap_preserves_multiset(a@, i as int, min_idx as int);
            sorted_prefix_preserved_after_swap(a@, i as int, min_idx as int);
            extend_sorted_prefix(a@, i as int, min_idx as int);
        }
        
        // Perform swap
        a.set(i, min_val);
        a.set(min_idx, temp);
        
        proof {
            // After swap, the sorted portion extends by one
            assert(is_sorted(a@, 0, (i + 1) as int));
            
            // Maintain invariant that sorted prefix elements are <= all suffix elements
            assert forall|j: int, k: int| 0 <= j < (i + 1) as int && (i + 1) as int <= k < n as int implies #[trigger] a@[j] <= #[trigger] a@[k] by {
                if j < i as int {
                    // j is in old sorted prefix
                    assert(0 <= j < i as int);
                    assert(i as int <= k < n as int);
                    assert(0 <= j < a@.len());
                    assert(0 <= k < a@.len());
                    // This was maintained by the loop invariant before the swap
                    // and the swap only affects positions i and min_idx where min_idx >= i
                } else {
                    // j == i
                    assert(j == i as int);
                    assert(0 <= j < a@.len());
                    assert(0 <= k < a@.len());
                    assert(a@[j] == min_val);
                    // min_val is minimum of a[i..n] by postcondition of find_min
                    // So a@[j] <= a@[k] for all k in [i+1, n)
                }
            }
        }
        
        i = i + 1;
    }
    
    proof {
        // At end of loop, i == n - 1, so sorted from 0 to n-1
        // Need to show sorted from 0 to n
        assert(i == n - 1);
        assert(n >= 1);
        
        // We have is_sorted(a@, 0, n-1)
        // We need is_sorted(a@, 0, n)
        
        assert forall|j: int, k: int| 0 <= j < k < n as int implies a@[j] <= a@[k] by {
            if k < (n - 1) as int {
                // Both j and k are in [0, n-1), covered by is_sorted(a@, 0, (n-1) as int)
                assert(is_sorted(a@, 0, (n - 1) as int));
                assert(0 <= j < k < (n - 1) as int);
                assert(0 <= j < a@.len());
                assert(0 <= k < a@.len());
            } else {
                // k == n - 1
                assert(k == (n - 1) as int);
                assert(0 <= j < (n - 1) as int);
                assert((n - 1) as int < n as int);
                assert(0 <= j < a@.len());
                assert(0 <= k < a@.len());
                // From the loop invariant at termination
            }
        }
        
        assert(is_sorted(a@, 0, n as int));
    }
}
// </vc-code>

fn main() {}

}