// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): placeholder, no change */
// </vc-helpers>

// <vc-spec>
fn longest_increasing_subsequence(nums: &Vec<i32>) -> (result: i32)
    ensures
        result >= 0,
        result <= nums.len() as i32,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Ensured all loop ranges are within bounds and assertions are correctly placed, ensuring `dp` remains synchronized with `n`. */
{
    let n = nums.len() as int;
    if n == 0 {
        return 0;
    }

    let mut dp: Vec<i32> = Vec::new();
    verus_proof_expr!{{
        dp.set_verifier_nondet(); // To allow modifying dp later without triggering 'spec_sealed' errors initially.
        dp.clear(); // Clear any initial nondet content.
    }}

    let mut initial_dp_value: int = 0;
    while initial_dp_value < n
        invariant
            dp.len() == initial_dp_value as nat,
            initial_dp_value >= 0,
            initial_dp_value <= n,
        decreases (n - initial_dp_value) as int
    {
        dp.push(1);
        initial_dp_value = initial_dp_value + 1;
    }

    assert(dp.len() == n as nat);
    let mut max_len = 1;
    if n > 0 { // Ensure max_len is at least 1 only if n > 0
        max_len = 1; 
    } else {
        max_len = 0;
    }

    for i in 0..n {
        assert(dp.len() == n as nat);
        assert(0 <= i && i < n);

        for j in 0..i {
            assert(0 <= j && j < n);
            assert(0 <= i && i < n);

            let num_i = nums.op_idx(i as nat);
            let num_j = nums.op_idx(j as nat);

            if num_i > num_j {
                let current_dp_j = dp.op_idx(j as nat);
                let current_dp_i = dp.op_idx(i as nat);

                if current_dp_j + 1 > current_dp_i {
                    dp.set(i as nat, current_dp_j + 1);
                }
            }
        }
        let current_dp_i = dp.op_idx(i as nat);
        if current_dp_i > max_len {
            max_len = current_dp_i;
        }
    }

    max_len
}
// </vc-code>

}
fn main() {}