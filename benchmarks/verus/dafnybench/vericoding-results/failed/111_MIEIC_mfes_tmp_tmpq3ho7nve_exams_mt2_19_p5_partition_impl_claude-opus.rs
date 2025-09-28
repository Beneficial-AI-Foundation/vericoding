use vstd::prelude::*;

verus! {

type T = int; // example

 // Partitions a nonempty array 'a', by reordering the elements in the array,
// so that elements smaller than a chosen pivot are placed to the left of the
// pivot, and values greater or equal than the pivot are placed to the right of 
// the pivot. Returns the pivot position.

// <vc-helpers>
// No additional helpers needed
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
    let pivot = a[0];
    let mut i: usize = 1;
    let mut j: usize = a.len() - 1;
    
    while i <= j
        invariant
            1 <= i <= a.len(),
            j < a.len(),
            i <= j + 1,
            a[0] == pivot,
            forall|k: int| 1 <= k < i ==> a[k] < pivot,
            forall|k: int| j < k < a.len() ==> a[k] >= pivot,
            a@.to_multiset() == old(a)@.to_multiset(),
    {
        if a[i] < pivot {
            i = i + 1;
        } else if a[j] >= pivot {
            j = j - 1;
        } else {
            // a[i] >= pivot && a[j] < pivot, so swap them
            proof {
                assert(a@.to_multiset() =~= a@.to_multiset());
            }
            let temp = a[i];
            a.set(i, a[j]);
            proof {
                assert(a@.to_multiset() =~= old(a)@.to_multiset().insert(a@[j as int]).remove(temp));
            }
            a.set(j, temp);
            proof {
                assert(a@.to_multiset() =~= old(a)@.to_multiset());
            }
            i = i + 1;
            j = j - 1;
        }
    }
    
    // Now place the pivot in its final position
    // After the loop, elements [1, i) are < pivot and elements (j+1, len) are >= pivot
    // The pivot should go at position i-1
    let pivot_pos = i - 1;
    
    if pivot_pos != 0 {
        proof {
            assert(a@.to_multiset() =~= a@.to_multiset());
        }
        let temp = a[0];
        a.set(0, a[pivot_pos]);
        proof {
            assert(a@.to_multiset() =~= old(a)@.to_multiset().insert(a@[pivot_pos as int]).remove(temp));
        }
        a.set(pivot_pos, temp);
        proof {
            assert(a@.to_multiset() =~= old(a)@.to_multiset());
            assert(a[pivot_pos as int] == pivot);
            assert(forall|k: int| 0 <= k < pivot_pos ==> a[k] < a[pivot_pos as int]);
            assert(forall|k: int| pivot_pos < k < a.len() ==> a[k] >= a[pivot_pos as int]);
        }
    } else {
        proof {
            assert(pivot_pos == 0);
            assert(a[0] == pivot);
            assert(forall|k: int| 0 <= k < pivot_pos ==> a[k] < a[pivot_pos as int]);
            assert(forall|k: int| pivot_pos < k < a.len() ==> a[k] >= a[pivot_pos as int]);
        }
    }
    
    pivot_pos
}
// </vc-code>

fn main() {}

}