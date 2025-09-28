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
// Helper lemma to prove that swapping elements preserves sortedness of a prefix
proof fn lemma_swap_preserves_sorted_prefix(a: Seq<i32>, b: Seq<i32>, i: int, j: int, end: int)
    requires
        0 <= i < end <= a.len(),
        0 <= j < a.len(),
        a.len() == b.len(),
        forall|k: int| 0 <= k < a.len() && k != i && k != j ==> a[k] == b[k],
        a[i] == b[j],
        a[j] == b[i],
        is_sorted(a, 0, i),
        forall|k: int| 0 <= k < i ==> a[k] <= a[j],
    ensures
        is_sorted(b, 0, i + 1),
{
    assert(forall|x: int, y: int| 0 <= x < y < i + 1 ==> b[x] <= b[y]) by {
        assert(forall|x: int, y: int| 0 <= x < y < i ==> b[x] <= b[y]);
        assert(forall|x: int| 0 <= x < i ==> b[x] == a[x]);
        assert(b[i] == a[j]);
        assert(forall|x: int| 0 <= x < i ==> a[x] <= a[j]);
    };
}

// Helper lemma to prove that if we have a minimum element and swap it to the front,
// the resulting array has the minimum at the front
proof fn lemma_min_swap_front(a: Seq<i32>, b: Seq<i32>, min_idx: int, front: int, end: int)
    requires
        0 <= front <= min_idx < end <= a.len(),
        a.len() == b.len(),
        forall|k: int| 0 <= k < a.len() && k != front && k != min_idx ==> a[k] == b[k],
        a[front] == b[min_idx],
        a[min_idx] == b[front],
        forall|k: int| front <= k < end ==> a[k] >= a[min_idx],
    ensures
        forall|k: int| front < k < end ==> b[k] >= b[front],
{
    assert(forall|k: int| front < k < end ==> b[k] >= b[front]) by {
        assert(b[front] == a[min_idx]);
        assert(forall|k: int| front <= k < end ==> a[k] >= a[min_idx]);
        assert(forall|k: int| front < k < end && k != min_idx ==> b[k] == a[k]);
        assert(b[min_idx] == a[front]);
        assert(a[front] >= a[min_idx]);
    };
}

// Helper lemma for multiset preservation after swap
proof fn lemma_swap_preserves_multiset(a: Seq<i32>, b: Seq<i32>, i: int, j: int)
    requires
        0 <= i < a.len(),
        0 <= j < a.len(),
        a.len() == b.len(),
        forall|k: int| 0 <= k < a.len() && k != i && k != j ==> a[k] == b[k],
        a[i] == b[j],
        a[j] == b[i],
    ensures
        a.to_multiset() == b.to_multiset(),
{
    assert(a.to_multiset() =~= b.to_multiset());
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
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            is_sorted(a@, 0, i as int),
            forall|p: int, q: int| 0 <= p < i && i <= q < a@.len() ==> a@[p] <= a@[q],
            a@.to_multiset() == old(a)@.to_multiset(),
        decreases a.len() - i,
    {
        if i + 1 < a.len() {
            let min_idx = find_min(a, i, a.len());
            
            // Store the old sequence before swap
            let old_seq = a@;
            
            // Swap elements at positions i and min_idx
            let temp = a[i];
            let min_val = a[min_idx];
            a.set(i, min_val);
            a.set(min_idx, temp);
            
            // Prove that the swap preserves the invariants
            proof {
                let new_seq = a@;
                
                // Establish swap relationship
                assert(old_seq[i as int] == new_seq[min_idx as int]);
                assert(old_seq[min_idx as int] == new_seq[i as int]);
                assert(forall|k: int| 0 <= k < old_seq.len() && k != i && k != min_idx ==> old_seq[k] == new_seq[k]);
                
                // Apply lemmas
                lemma_swap_preserves_multiset(old_seq, new_seq, i as int, min_idx as int);
                
                // For sorted prefix lemma, we need to establish the precondition about minimum
                assert(forall|k: int| 0 <= k < i ==> old_seq[k] <= old_seq[min_idx as int]);
                lemma_swap_preserves_sorted_prefix(old_seq, new_seq, i as int, min_idx as int, (i + 1) as int);
                
                // For the min swap front lemma
                lemma_min_swap_front(old_seq, new_seq, min_idx as int, i as int, a@.len() as int);
                
                // Establish the cross-section invariant
                assert(forall|p: int, q: int| 0 <= p < i + 1 && i + 1 <= q < a@.len() ==> a@[p] <= a@[q]) by {
                    assert(forall|q: int| i + 1 <= q < a@.len() ==> new_seq[i as int] <= new_seq[q]);
                };
            }
        }
        i += 1;
    }
}
// </vc-code>

fn main() {}

}