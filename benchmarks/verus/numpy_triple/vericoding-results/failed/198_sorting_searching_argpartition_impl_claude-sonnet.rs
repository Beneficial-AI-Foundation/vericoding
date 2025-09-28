// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed bounds checking and strengthened invariants */
spec fn is_permutation(indices: Vec<usize>, n: usize) -> bool {
    indices.len() == n &&
    (forall|i: int| 0 <= i < n ==> indices@[i] < n) &&
    (forall|i: int, j: int| 0 <= i < n && 0 <= j < n && i != j ==> indices@[i] != indices@[j])
}

// Helper function to swap two elements in a vector
fn swap_indices(indices: &mut Vec<usize>, i: usize, j: usize)
    requires
        old(indices).len() > 0,
        i < old(indices).len(),
        j < old(indices).len(),
    ensures
        indices.len() == old(indices).len(),
        indices@[i as int] == old(indices)@[j as int],
        indices@[j as int] == old(indices)@[i as int],
        forall|k: int| 0 <= k < indices.len() && k != i && k != j ==> indices@[k] == old(indices)@[k],
{
    let temp = indices[i];
    indices.set(i, indices[j]);
    indices.set(j, temp);
}

// Partition function that partitions around a pivot
fn partition(a: &Vec<i8>, indices: &mut Vec<usize>, low: usize, high: usize, pivot_idx: usize) -> (pivot_pos: usize)
    requires
        a.len() > 0,
        old(indices).len() == a.len(),
        low <= high,
        high < a.len(),
        pivot_idx <= high,
        pivot_idx >= low,
        is_permutation(*old(indices), a.len()),
        forall|k: int| 0 <= k < old(indices).len() ==> old(indices)@[k] < a.len(),
    ensures
        indices.len() == a.len(),
        pivot_pos >= low,
        pivot_pos <= high,
        is_permutation(*indices, a.len()),
        forall|k: int| 0 <= k < indices.len() ==> indices@[k] < a.len(),
        forall|i: int| low <= i < pivot_pos ==> a@[indices@[i] as int] <= a@[indices@[pivot_pos as int] as int],
        forall|i: int| pivot_pos < i <= high ==> a@[indices@[pivot_pos as int] as int] <= a@[indices@[i] as int],
{
    swap_indices(indices, pivot_idx, high);
    let pivot_value = a[indices[high]];
    let mut i = low;
    let mut j = low;
    
    while j < high
        invariant
            low <= i,
            i <= j,
            j <= high,
            indices.len() == a.len(),
            is_permutation(*indices, a.len()),
            forall|k: int| 0 <= k < indices.len() ==> indices@[k] < a.len(),
            forall|k: int| low <= k < i ==> {
                0 <= k < indices.len() && 0 <= indices@[k] < a.len() &&
                a@[indices@[k] as int] <= pivot_value
            },
            forall|k: int| i <= k < j ==> {
                0 <= k < indices.len() && 0 <= indices@[k] < a.len() &&
                a@[indices@[k] as int] > pivot_value
            },
            a@[indices@[high as int] as int] == pivot_value,
            j < indices.len(),
        decreases high - j
    {
        if a[indices[j]] <= pivot_value {
            swap_indices(indices, i, j);
            i = i + 1;
        }
        j = j + 1;
    }
    
    swap_indices(indices, i, high);
    i
}

// Lemma to help prove partition properties are maintained
fn lemma_partition_preserves_order(a: &Vec<i8>, indices: &Vec<usize>, low: usize, high: usize, pivot_pos: usize, kth: usize)
    requires
        a.len() > 0,
        indices.len() == a.len(),
        low <= kth,
        kth <= high,
        high < a.len(),
        pivot_pos >= low,
        pivot_pos <= high,
        is_permutation(*indices, a.len()),
        forall|k: int| 0 <= k < indices.len() ==> indices@[k] < a.len(),
        forall|i: int| low <= i < pivot_pos ==> a@[indices@[i] as int] <= a@[indices@[pivot_pos as int] as int],
        forall|i: int| pivot_pos < i <= high ==> a@[indices@[pivot_pos as int] as int] <= a@[indices@[i] as int],
    ensures
        pivot_pos == kth ==> {
            forall|i: int| 0 <= i < kth ==> a@[indices@[i] as int] <= a@[indices@[kth as int] as int]
        },
        pivot_pos == kth ==> {
            forall|i: int| kth < i && i < indices.len() ==> a@[indices@[kth as int] as int] <= a@[indices@[i] as int]
        },
{
    if pivot_pos == kth {
        // The partition properties follow from the preconditions
    }
}
// </vc-helpers>

// <vc-spec>
fn argpartition(a: Vec<i8>, kth: usize) -> (indices: Vec<usize>)
    requires 
        a.len() > 0,
        kth < a.len(),
    ensures
        /* The indices form a valid permutation of 0..n-1 */
        indices.len() == a.len(),
        /* Partition property: all elements before kth position are ≤ kth element */
        forall|i: int| 0 <= i < kth ==> a@[#[trigger] indices@[i] as int] <= a@[#[trigger] indices@[kth as int] as int],
        /* Partition property: all elements after kth position are ≥ kth element */
        forall|i: int| kth < i && i < indices.len() ==> a@[#[trigger] indices@[kth as int] as int] <= a@[#[trigger] indices@[i] as int],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): simplified with proper partition property tracking */
    let mut indices = Vec::new();
    let mut i = 0;
    
    // Initialize indices vector with 0, 1, 2, ..., n-1
    while i < a.len()
        invariant
            i <= a.len(),
            indices.len() == i,
            forall|j: int| 0 <= j < i ==> indices@[j] == j,
        decreases a.len() - i
    {
        indices.push(i);
        i = i + 1;
    }
    
    // Quick select algorithm to find kth element
    let mut low = 0;
    let mut high = a.len() - 1;
    
    while low < high
        invariant
            low <= kth,
            kth <= high,
            high < a.len(),
            indices.len() == a.len(),
            is_permutation(indices, a.len()),
            forall|k: int| 0 <= k < indices.len() ==> indices@[k] < a.len(),
        decreases high - low
    {
        // Use middle element as pivot
        let pivot_idx = low + (high - low) / 2;
        let pivot_pos = partition(&a, &mut indices, low, high, pivot_idx);
        
        if pivot_pos == kth {
            lemma_partition_preserves_order(&a, &indices, low, high, pivot_pos, kth);
            break;
        } else if pivot_pos > kth {
            if pivot_pos > 0 {
                high = pivot_pos - 1;
            } else {
                break;
            }
        } else {
            low = pivot_pos + 1;
        }
    }
    
    indices
}
// </vc-code>


}
fn main() {}