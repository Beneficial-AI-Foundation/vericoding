// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 4): Fixed quantifier trigger issue by adding #[trigger] annotation */
    let n = a.len();
    let mut indices = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            indices.len() == i,
            i <= n,
            forall|j: int, k: int| 0 <= j < k && k < i ==> indices@[j] != indices@[k],
            forall|j: int| 0 <= j < i ==> 0 <= #[trigger] indices@[j] < n,
        decreases n - i
    {
        indices.push(i);
        i = i + 1;
    }
    
    let pivot_val = a[kth];
    let mut left: usize = 0;
    let mut right: usize = n - 1;
    
    while left < right
        invariant
            indices.len() == n,
            left <= right,
            right < n,
            forall|i: int| 0 <= i < left ==> a@[indices@[i] as int] <= a@[indices@[kth as int] as int],
            forall|i: int| right < i && i < n ==> a@[indices@[kth as int] as int] <= a@[indices@[i] as int],
        decreases right - left
    {
        if a[indices[left]] <= pivot_val {
            left = left + 1;
        } else if a[indices[right]] >= pivot_val {
            if right > 0 {
                right = right - 1;
            } else {
                break;
            }
        } else {
            let temp = indices[left];
            indices.set(left, indices[right]);
            indices.set(right, temp);
            left = left + 1;
            if right > 0 {
                right = right - 1;
            }
        }
    }
    
    let mut kth_pos: usize = 0;
    let mut found = false;
    let mut j: usize = 0;
    while j < n
        invariant
            j <= n,
            indices.len() == n,
            !found ==> forall|k: int| 0 <= k < j ==> indices@[k] != kth,
            found ==> kth_pos < n && indices@[kth_pos as int] == kth,
        decreases n - j
    {
        if indices[j] == kth {
            kth_pos = j;
            found = true;
            break;
        }
        j = j + 1;
    }
    
    if kth_pos != kth {
        let temp = indices[kth];
        indices.set(kth, indices[kth_pos]);
        indices.set(kth_pos, temp);
    }
    
    indices
}
// </vc-code>


}
fn main() {}