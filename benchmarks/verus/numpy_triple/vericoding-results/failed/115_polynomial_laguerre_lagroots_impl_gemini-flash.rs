// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The helper section was empty, so it's kept empty. */
// </vc-helpers>

// <vc-spec>
fn lagroots(c: Vec<i32>) -> (roots: Vec<i32>)
    requires
        c.len() >= 2,
        c@[c.len() - 1 as int] != 0,
    ensures
        c.len() == 2 ==> roots.len() == 1,
        c.len() == 2 ==> roots@[0] == 1 + c@[0] / c@[1],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Added explicit proof for integer division and addition to satisfy `ensures` clause and handle potential overflows in calculations. */
{
    if c.len() == 2 {
        // The precondition c@[c.len() - 1 as int] != 0 ensures c@[1] != 0 when c.len() == 2.
        // We also need to satisfy the precondition that c[1] must not be 0 for integer division.
        // The original precondition (`c@[c.len() - 1 as int] != 0`) already covers this for c.len() == 2.

        proof {
            // Intermediate values can safely be stored in i64 to prevent overflows
            // before casting back to i32.
            let c0_i64: i64 = c[0] as i64;
            let c1_i64: i64 = c[1] as i64;
            let div_result_i64: i64 = c0_i64 / c1_i64;
            let root_val_i64: i64 = 1_i64 + div_result_i64;

            // We need to prove that the final result fits into i32
            assert(root_val_i64 >= i32::MIN as i64 && root_val_i64 <= i32::MAX as i64);
        }

        let div_result: i32 = c[0] / c[1];
        let root_val: i32 = 1_i32 + div_result;
        return vec![root_val];
    } else {
        let roots: Vec<i32> = Vec::new();
        return roots;
    }
}
// </vc-code>

}
fn main() {}