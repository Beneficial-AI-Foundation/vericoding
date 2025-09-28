use vstd::prelude::*;

verus! {

type T = int; // example

 // Partitions a nonempty array 'a', by reordering the elements in the array,
// so that elements smaller than a chosen pivot are placed to the left of the
// pivot, and values greater or equal than the pivot are placed to the right of 
// the pivot. Returns the pivot position.

// <vc-helpers>
fn swap(a: &mut Vec<T>, i: usize, j: usize)
    requires
        i < old(a).len(),
        j < old(a).len(),
    ensures
        a.len() == old(a).len(),
        a[i as int] == old(a)[j as int],
        a[j as int] == old(a)[i as int],
        forall|k: int| 0 <= k < a.len() && k != i && k != j ==> a[k] == old(a)[k],
        a@.to_multiset() == old(a)@.to_multiset(),
{
    let temp = a[i];
    a.set(i, a[j]);
    a.set(j, temp);
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
    let pivot_value = a[0];
    let mut i = 0usize;
    let mut j = len - 1;
    
    while i < j
        invariant
            0 <= i <= j < len,
            a.len() == len,
            a@.to_multiset() == old(a)@.to_multiset(),
            forall|k: int| 0 <= k < i ==> a[k] < pivot_value,
            forall|k: int| j < k < len ==> a[k] >= pivot_value,
        decreases j - i,
    {
        while i < j && a[i] < pivot_value
            invariant
                0 <= i <= j < len,
                a.len() == len,
                a@.to_multiset() == old(a)@.to_multiset(),
                forall|k: int| 0 <= k < i ==> a[k] < pivot_value,
                forall|k: int| j < k < len ==> a[k] >= pivot_value,
        {
            i = i + 1;
        }
        
        while i < j && a[j] >= pivot_value
            invariant
                0 <= i <= j < len,
                a.len() == len,
                a@.to_multiset() == old(a)@.to_multiset(),
                forall|k: int| 0 <= k < i ==> a[k] < pivot_value,
                forall|k: int| j < k < len ==> a[k] >= pivot_value,
        {
            j = j - 1;
        }
        
        if i < j {
            swap(a, i, j);
            i = i + 1;
            j = j - 1;
        }
    }
    
    let final_pos = if a[i] < pivot_value { i + 1 } else { i };
    
    if final_pos != 0 && final_pos < a.len() {
        swap(a, 0, final_pos);
    }
    
    proof {
        if final_pos == 0 {
            assert(forall|k: int| 0 <= k < final_pos ==> a[k] < a[final_pos as int]);
            assert(forall|k: int| final_pos < k < a.len() ==> a[k] >= a[final_pos as int]);
        } else if final_pos == len {
            assert(final_pos > 0);
            assert(forall|k: int| 0 <= k < final_pos ==> a[k] < pivot_value);
            assert(final_pos == len);
        } else {
            assert(final_pos < len);
            assert(forall|k: int| 0 <= k < final_pos ==> a[k] < a[final_pos as int]);
            assert(forall|k: int| final_pos < k < a.len() ==> a[k] >= a[final_pos as int]);
        }
    }
    
    if final_pos == len { 0 } else { final_pos }
}
// </vc-code>

fn main() {}

}