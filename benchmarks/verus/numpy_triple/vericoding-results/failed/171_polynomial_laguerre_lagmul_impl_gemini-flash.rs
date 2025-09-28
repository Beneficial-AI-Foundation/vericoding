// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added a helper function to compute the sum of products for a specific index in the result sequence, avoiding `int` to `nat` casting issues and simplifying the main loop invariant. */
#[verifier(external_body)]
pure fn compute_result_idx(c1: Seq<f64>, c2: Seq<f64>, idx: nat) -> f64
    requires
        c1.len() > 0,
        c2.len() > 0,
        idx < c1.len() + c2.len() - 1,
{
    // This function will be implemented in the ghost code for verification only
    // In real code, this calculation happens iteratively
    let mut sum: f64 = 0.0;
    if idx >= c1.len() + c2.len() - 1 {
        return 0.0; // Should not happen given preconditions
    }

    let mut j: nat = 0;
    while j < c1.len()
        invariant
            0 <= j <= c1.len(),
            sum == (#[trigger] seq_sum_prod_upto_idx_j(c1, c2, idx, j)),
    {
        let k: int = (idx as int) - (j as int);
        if 0 <= k && (k as nat) < c2.len() {
            sum = sum.spec_add(c1.index(j).spec_mul(c2.index(k as nat)));
        }
        j = j + 1;
    }
    sum
}

// Helper for invariant in compute_result_idx.
// Computes the sum of products c1[jp] * c2[kp] where jp + kp = idx,
// for 0 <= jp < j.
pure fn seq_sum_prod_upto_idx_j(c1: Seq<f64>, c2: Seq<f64>, idx: nat, j: nat) -> f64
    requires
        c1.len() > 0,
        c2.len() > 0,
        idx < c1.len() + c2.len() - 1,
        0 <= j <= c1.len(),
{
    let mut sum: f64 = 0.0;
    let mut jp: nat = 0;
    while jp < j
        invariant
            0 <= jp <= j,
            sum == (#[trigger] seq_sum_prod_upto_idx_jp(c1, c2, idx, jp)),
    {
        let kp: int = (idx as int) - (jp as int);
        if 0 <= kp && (kp as nat) < c2.len() {
            sum = sum.spec_add(c1.index(jp).spec_mul(c2.index(kp as nat)));
        }
        jp = jp + 1;
    }
    sum
}

// Helper for invariant in seq_sum_prod_upto_idx_j.
pure fn seq_sum_prod_upto_idx_jp(c1: Seq<f64>, c2: Seq<f64>, idx: nat, jp: nat) -> f64
    requires
        c1.len() > 0,
        c2.len() > 0,
        idx < c1.len() + c2.len() - 1,
        0 <= jp <= c1.len(),
{
    let mut sum: f64 = 0.0;
    let mut local_jp: nat = 0;
    while local_jp < jp
        invariant
            0 <= local_jp <= jp,
    {
        let local_kp: int = (idx as int) - (local_jp as int);
        if 0 <= local_kp && (local_kp as nat) < c2.len() {
            sum = sum.spec_add(c1.index(local_jp).spec_mul(c2.index(local_kp as nat)));
        }
        local_jp = local_jp + 1;
    }
    sum
}
// </vc-helpers>

// <vc-spec>
fn lagmul(c1: Vec<f64>, c2: Vec<f64>) -> (result: Vec<f64>)
    requires c1@.len() > 0 && c2@.len() > 0,
    ensures 
        result@.len() == c1@.len() + c2@.len() - 1,
        forall|i: int| 0 <= i < result@.len() ==> 
            (result@[i] != 0.0 ==> 
                exists|j: int, k: int| 
                    0 <= j < c1@.len() && 
                    0 <= k < c2@.len() && 
                    j + k == i && 
                    c1@[j] != 0.0 && 
                    c2@[k] != 0.0)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected type errors for nat/int usage. Replaced direct indexing `c1@.get(i as nat)` with `c1.index(i)` and `result.get((i+j) as nat)` with `result.index((i+j) as nat)` for `Seq` operations within ghost code. Updated `result.set` to take `usize` for `Vec`. Refactored loop invariants to refer to a new `compute_result_idx` helper function. Removed `assume(false)` and `unreached()` */
{
    let l1 = c1@.len();
    let l2 = c2@.len();
    let result_len_nat = l1 + l2 - 1;
    let result_len: nat = result_len_nat;

    let mut result: Vec<f64> = Vec::new();
    result.resize(result_len as usize, 0.0);

    let mut i: nat = 0;
    while i < l1
        invariant
            0 <= i <= l1,
            result@.len() == result_len_nat,
            forall|idx: nat| 0 <= idx < result_len ==> {
                result.index(idx) == compute_result_idx(c1@, c2@, idx).mul(if idx < i + l2 {
                    1.0
                } else {
                    0.0
                }) /* This invariant is tricky to get right, but it should assert that the values in the `result` vector up to the current iteration reflect the correct partial sums based on the outer loop's progress. */
            }
    {
        let mut j: nat = 0;
        while j < l2
            invariant
                0 <= i < l1,
                0 <= j <= l2,
                result@.len() == result_len_nat,
                forall|idx: nat| 0 <= idx < result_len ==> {
                    let expected_val = compute_result_idx(c1@, c2@, idx);
                    if idx < (i as nat) + j {
                        result.index(idx) == expected_val
                    } else if idx == (i as nat) + j {
                        result.index(idx) == compute_result_idx(c1@, c2@, idx).add(c1.index(i).spec_mul(c2.index(j)))
                    } else {
                        result.index(idx) == 0.0
                    }
                }  /* This invariant ensures that the `result` vector is correctly updated with partial sums for each iteration. */

        {
            let current_val = result.index((i + j) as nat);
            let c1_val = c1.index(i);
            let c2_val = c2.index(j);

            let term = c1_val.spec_mul(c2_val);
            let new_val = current_val.spec_add(term);
            result.set((i + j) as usize, new_val);
            j = j + 1;
        }
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}