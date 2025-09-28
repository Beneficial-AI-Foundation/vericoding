use vstd::prelude::*;

verus! {

type T = int; // example

 // Partitions a nonempty array 'a', by reordering the elements in the array,
// so that elements smaller than a chosen pivot are placed to the left of the
// pivot, and values greater or equal than the pivot are placed to the right of 
// the pivot. Returns the pivot position.

// <vc-helpers>
fn do_swap<T>(a: &mut Vec<T>, i: usize, j: usize)
    requires
        i < old(a).len(),
        j < old(a).len(),
    ensures
        a@.to_multiset() == old(a)@.to_multiset(),
        a@[i as int] == old(a)@[j as int],
        a@[j as int] == old(a)@[i as int],
        forall |k: int| 0 <= k < old(a).len() && k != i as int && k != j as int ==> a@[k] == old(a)@[k],
{
    proof {
        let old_a_seq = old(a)@;
        let val_i = old_a_seq.index(i as int);
        let val_j = old_a_seq.index(j as int);
        
        assert(old_a_seq.to_multiset() == (old_a_seq.update(i as int, val_j)).update(j as int, val_i).to_multiset());
    }

    let val_at_i = a[i];
    a[i] = a[j];
    a[j] = val_at_i;

    proof {
        assert(a@[i as int] == old(a)@[j as int]);
        assert(a@[j as int] == old(a)@[i as int]);
        assert(a@.to_multiset() == old(a)@.to_multiset());
    }
}
// </vc-helpers>

// <vc-spec>
fn partition(a: &mut Vec<T>) -> (pivotPos: usize)
    requires 
        old(a).len() > 0,
    ensures 
        pivotPos < a.len(),
        forall|i: int| 0 <= i < pivotPos ==> a[i] < a[pivotPos as int],
        forall|i: int| pivotPos < i < a.len() ==> a[i] >= a[pivotPos as int],
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    let len = a.len();
    assert(len > 0);

    let pivot_value = a[len - 1]; // Choose the last element as pivot
    let mut i: usize = 0; // i is the boundary of elements <= pivot
    let mut j: usize = 0; // j iterates through the array

    while j < len - 1
        invariant
            0 <= i && i <= j && j < len,
            a.len() == len,
            a@[len as int - 1] == old(a)@[len as int - 1], // Pivot is unchanged until swap
            forall k: int. 0 <= k < i ==> a@[k] < old(a)@[len as int - 1], // Elements before i are less than pivot
            forall k: int. i <= k < j ==> a@[k] >= old(a)@[len as int - 1], // Elements between i and j are >= pivot
            a@.to_multiset() == old(a)@.to_multiset(), // Multiset identity
    {
        if a[j] < pivot_value {
            do_swap(a, i, j);
            proof {
                assert(a@[i as int] == old(a)@[j as int]);
                assert(a@[j as int] == old(a)@[i as int]);
            }
            i = i + 1;
        }
        j = j + 1;
    }

    do_swap(a, i, len - 1);

    let pivot_pos = i;

    proof {
        assert(pivot_pos < a.len());
        assert(i <= len - 1);

        let old_a_seq = old(a)@;
        assert forall |k: int| 0 <= k < pivot_pos implies a@[k] < a[pivot_pos as int] by {
            assert(a@[pivot_pos as int] == old_a_seq.index(len as int - 1));
            if k < i {
                assert(a@[k] < old_a_seq.index(len as int - 1));
            } else {
                // This case should not happen if the loop invariant holds
            }
        }

        assert forall |k: int| pivot_pos < k < a.len() implies a@[k] >= a[pivot_pos as int] by {
            assert(a@[pivot_pos as int] == old_a_seq.index(len as int - 1));
            if k == len - 1 {
                // The element at len-1 is the original element at i (before final swap)
                // which must be >= the pivot_value (original element at len-1) if i was less than len-1
                // or it is the pivot value if i == len-1
                assert(a@[len as int - 1] == old_a_seq.index(i as int));
                assert(old_a_seq.index(i as int) >= old_a_seq.index(len as int - 1)); // From invariant, or because it's the pivot itself
                assert(a@[len as int - 1] >= a@[pivot_pos as int]);
            } else {
                if k >= i && k < j {
                    assert(a@[k] >= old_a_seq.index(len as int - 1));
                    assert(a@[k] >= a@[pivot_pos as int]);
                } else if k == j {
                    // This case should not happen if the loop invariant holds strictly
                }
            }
        }
    }

    pivot_pos
}
// </vc-code>

fn main() {}

}