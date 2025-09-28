// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix compilation errors and improve helper functions */
spec fn is_sorted_partition(a: Seq<i8>, indices: Seq<usize>, pivot_pos: int) -> bool {
    (forall|i: int| 0 <= i < pivot_pos ==> a[indices[i] as int] <= a[indices[pivot_pos] as int]) &&
    (forall|i: int| pivot_pos < i && i < indices.len() ==> a[indices[pivot_pos] as int] <= a[indices[i] as int])
}

spec fn permutation_property(indices: Seq<usize>, n: nat) -> bool {
    indices.len() == n &&
    (forall|i: int| 0 <= i < n ==> 0 <= indices[i] < n) &&
    (forall|x: int| 0 <= x < n ==> exists|i: int| 0 <= i < n &&#[trigger] indices[i] == x)
}

fn cast_usize_to_nat(x: usize) -> nat {
    x as nat
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
    /* code modified by LLM (iteration 5): Fix compilation errors and implement proper verification */
    let n = a.len();
    let mut indices = Vec::new();
    let mut i = 0;
    while i < n 
        invariant
            indices.len() == i,
            forall|j: int| 0 <= j < i ==> indices@[j] == j,
    {
        indices.push(i);
        i += 1;
    }
    
    let kth_val = kth as nat;
    let mut left = 0;
    let mut right = n - 1;
    
    while left < right {
        invariant
            0 <= left,
            right < n,
            left <= right,
        decreases right - left,
        let pivot_index = (left + right) / 2;
        let pivot_value = a[indices[pivot_index]];
        let mut i = left;
        let mut j = right;
        
        while i <= j {
            invariant
                left <= i,
                j <= right,
            decreases j - i,
        {
            while i <= right && a[indices[i]] < pivot_value { i += 1; }
            while j >= left && a[indices[j]] > pivot_value { j -= 1; }
            
            if i <= j {
                indices.swap(i, j);
                i += 1;
                if j > 0 { j -= 1; }
            }
        }
        
        if kth <= j {
            right = j;
        } else if kth >= i {
            left = i;
        } else {
            break;
        }
    }
    
    indices
}
// </vc-code>


}
fn main() {}