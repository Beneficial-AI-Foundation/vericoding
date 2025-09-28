// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): changed ghost operations to exec operations for vector indexing and comparisons */
fn argpartition_helper(a: Vec<i8>, kth: usize) -> (indices: Vec<usize>)
    requires 
        a.len() > 0,
        kth < a.len(),
    ensures
        indices.len() == a.len(),
        forall|i: int| 0 <= i < kth ==> a@[#[trigger] indices@[i] as int] <= a@[#[trigger] indices@[kth as int] as int],
        forall|i: int| kth < i && i < indices.len() ==> a@[#[trigger] indices@[kth as int] as int] <= a@[#[trigger] indices@[i] as int],
{
    let n = a.len();
    let mut indices = Vec::with_capacity(n);
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            indices.len() == i,
    {
        indices.push(i);
        i = i + 1;
    }
    
    let mut pivot_idx = 0;
    let mut j = 0;
    while j < n
        invariant
            0 <= j <= n,
            0 <= pivot_idx <= j <= n,
            forall|i: int| 0 <= i < pivot_idx ==> a@[#[trigger] indices@[i] as int] <= a@[#[trigger] indices@[kth as int] as int],
            forall|i: int| pivot_idx <= i < j ==> a@[#[trigger] indices@[i] as int] >= a@[#[trigger] indices@[kth as int] as int],
        decreases (n - j)
    {
        if a[indices[j]] < a[indices[kth]] {
            let temp = indices[pivot_idx];
            indices[pivot_idx] = indices[j];
            indices[j] = temp;
            if kth == j {
                pivot_idx = pivot_idx + 1;
            } else if kth == pivot_idx {
                pivot_idx = pivot_idx + 1;
            }
        }
        j = j + 1;
    }
    
    indices
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
    /* code modified by LLM (iteration 2): call the fixed helper function */
    argpartition_helper(a, kth)
}
// </vc-code>


}
fn main() {}