// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn argsort(a: Vec<i8>) -> (result: Vec<usize>)
    ensures 
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> #[trigger] a@[result@[i] as int] <= #[trigger] a@[result@[j] as int],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added trigger annotations to fix quantifier inference */
    let n = a.len();
    let mut indices = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            indices.len() == i,
            i <= n,
            forall|k: int| 0 <= k < i ==> #[trigger] indices@[k] == k,
            forall|k: int| 0 <= k < i ==> 0 <= #[trigger] indices@[k] < n,
        decreases n - i
    {
        indices.push(i);
        i = i + 1;
    }
    
    let mut i: usize = 0;
    while i < n
        invariant
            indices.len() == n,
            i <= n,
            forall|k: int| 0 <= k < n ==> 0 <= #[trigger] indices@[k] < n,
            forall|k1: int, k2: int| 0 <= k1 < k2 < n && k2 < n - i ==> #[trigger] a@[indices@[k1] as int] <= #[trigger] a@[indices@[k2] as int],
            forall|k1: int, k2: int| n - i <= k1 < k2 < n ==> #[trigger] a@[indices@[k1] as int] <= #[trigger] a@[indices@[k2] as int],
            forall|k1: int, k2: int| 0 <= k1 < n - i && n - i <= k2 < n ==> #[trigger] a@[indices@[k1] as int] <= #[trigger] a@[indices@[k2] as int],
        decreases n - i
    {
        let mut j: usize = 0;
        while j < n - i - 1
            invariant
                indices.len() == n,
                j <= n - i - 1,
                i < n,
                forall|k: int| 0 <= k < n ==> 0 <= #[trigger] indices@[k] < n,
                forall|k1: int, k2: int| 0 <= k1 < k2 <= j ==> #[trigger] a@[indices@[k1] as int] <= #[trigger] a@[indices@[k2] as int],
                forall|k: int| 0 <= k <= j ==> #[trigger] a@[indices@[k] as int] <= #[trigger] a@[indices@[j as int] as int],
                forall|k1: int, k2: int| 0 <= k1 < k2 < n && k2 < n - i ==> #[trigger] a@[indices@[k1] as int] <= #[trigger] a@[indices@[k2] as int],
                forall|k1: int, k2: int| n - i <= k1 < k2 < n ==> #[trigger] a@[indices@[k1] as int] <= #[trigger] a@[indices@[k2] as int],
                forall|k1: int, k2: int| 0 <= k1 < n - i && n - i <= k2 < n ==> #[trigger] a@[indices@[k1] as int] <= #[trigger] a@[indices@[k2] as int],
            decreases n - i - 1 - j
        {
            let idx_j = indices[j];
            let idx_j_plus_1 = indices[j + 1];
            if a[idx_j] > a[idx_j_plus_1] {
                indices.set(j, idx_j_plus_1);
                indices.set(j + 1, idx_j);
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