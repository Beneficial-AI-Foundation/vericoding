// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn lexsort(keys: Vec<Vec<i8>>) -> (indices: Vec<u8>)
    requires 
        keys.len() > 0,
        keys.len() > 0 ==> keys[0].len() > 0,
        forall|i: int| 0 <= i < keys.len() ==> #[trigger] keys[i as int]@.len() == keys[0]@.len(),
    ensures
        indices@.len() == keys[0]@.len(),
        /* indices contains all values from 0 to n-1 exactly once */
        forall|i: int| 0 <= i < keys[0]@.len() ==> #[trigger] indices@.contains(i as u8),
        forall|i: int, j: int| 0 <= i < indices@.len() && 0 <= j < indices@.len() && i != j ==> indices[i as int] != indices[j as int]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type casting issues and loop invariants */
    let n = keys[0].len();
    assert(n <= 256); // Ensure n fits in u8
    
    let mut indices = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            indices@.len() == i as int,
            i <= n,
            n <= 256,
            forall|j: int| 0 <= j < i && j < 256 ==> #[trigger] indices@.contains(j as u8),
            forall|j: int, k: int| 0 <= j < indices@.len() && 0 <= k < indices@.len() && j != k ==> indices[j as int] != indices[k as int],
        decreases n - i
    {
        assert(i < 256);
        indices.push(i as u8);
        i = i + 1;
    }
    
    let mut i: usize = 0;
    while i < n
        invariant
            indices@.len() == n as int,
            i <= n,
            n <= 256,
            forall|j: int| 0 <= j < n && j < 256 ==> #[trigger] indices@.contains(j as u8),
            forall|j: int, k: int| 0 <= j < indices@.len() && 0 <= k < indices@.len() && j != k ==> indices[j as int] != indices[k as int],
        decreases n - i
    {
        let mut j: usize = i + 1;
        while j < n
            invariant
                indices@.len() == n as int,
                i < n,
                j <= n,
                n <= 256,
                forall|k: int| 0 <= k < n && k < 256 ==> #[trigger] indices@.contains(k as u8),
                forall|k: int, l: int| 0 <= k < indices@.len() && 0 <= l < indices@.len() && k != l ==> indices[k as int] != indices[l as int],
            decreases n - j
        {
            let mut should_swap = false;
            let mut k: usize = 0;
            while k < keys.len()
                invariant
                    k <= keys.len(),
                    i < indices@.len(),
                    j < indices@.len(),
                decreases keys.len() - k
            {
                assert(i < indices@.len());
                assert(j < indices@.len());
                let idx_i = indices[i] as usize;
                let idx_j = indices[j] as usize;
                assert(idx_i < keys[k]@.len());
                assert(idx_j < keys[k]@.len());
                if keys[k][idx_i] > keys[k][idx_j] {
                    should_swap = true;
                    break;
                } else if keys[k][idx_i] < keys[k][idx_j] {
                    break;
                }
                k = k + 1;
            }
            
            if should_swap {
                let temp = indices[i];
                indices.set(i, indices[j]);
                indices.set(j, temp);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    indices
}
// </vc-code>


}
fn main() {}