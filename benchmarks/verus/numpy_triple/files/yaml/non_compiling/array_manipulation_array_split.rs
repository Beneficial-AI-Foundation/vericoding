/* Split a vector into k sub-vectors.

When splitting a vector of length n into k sections:
- The first (n % k) sub-vectors have size ⌈n/k⌉ = (n + k - 1) / k
- The remaining sub-vectors have size ⌊n/k⌋ = n / k

This ensures all elements are distributed as evenly as possible,
with larger sub-vectors appearing first. */

use vstd::prelude::*;

verus! {
spec fn chunk_size(n: nat, k: nat, pos: nat) -> nat {
    if pos < n % k {
        (n + k - 1) / k
    } else {
        n / k
    }
}

spec fn cumulative_size(n: nat, k: nat, pos: nat) -> nat
    decreases pos
{
    if pos == 0 {
        0
    } else {
        cumulative_size(n, k, pos - 1) + chunk_size(n, k, pos - 1)
    }
}

fn array_split(v: Vec<f32>, k: usize) -> (result: Vec<Vec<f32>>)
    requires k > 0,
    ensures
        result.len() == k,
        forall|i: int| 0 <= i < k ==> result[i].len() == chunk_size(v.len() as nat, k as nat, i as nat),
        forall|i: int, j: int| 0 <= i < k && 0 <= j < result[i].len() ==> {
            let start_idx = cumulative_size(v.len() as nat, k as nat, i as nat);
            start_idx + j < v.len() && result[i][j] == v[(start_idx + j) as int]
        }
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}