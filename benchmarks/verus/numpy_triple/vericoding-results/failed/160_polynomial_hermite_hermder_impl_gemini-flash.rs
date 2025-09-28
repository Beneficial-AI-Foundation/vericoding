// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn hermder(c: Vec<i8>, m: usize, scl: i8) -> (result: Vec<i8>)
    ensures
        result.len() == if m >= c.len() { 0 } else { c.len() - m },
        m >= c.len() ==> result.len() == 0,
        m < c.len() ==> result.len() == c.len() - m,
        (m == 1 && c.len() > 0) ==> (
            forall|i: int| 0 <= i < result.len() ==> 
                result[i] as int == (scl as int) * (2 * ((i + 1) as int)) * (c[i + 1] as int)
        ),
        (m == 2 && c.len() > 1) ==> (
            forall|i: int| 0 <= i < result.len() ==>
                result[i] as int == (scl as int) * (scl as int) * (2 * ((i + 2) as int)) * (2 * ((i + 1) as int)) * (c[i + 2] as int)
        ),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Add an explicit check for the length of `c` before accessing `c[k+1]` or `c[k+2]` inside the forall statements to prevent out-of-bounds access. The existing constraints on `k` (0 <= k < result_vec.len()) are helpful, but the checks are needed to ensure `c[k+1]` and `c[k+2]` are always within bounds of `c`. Specifically, `k+1 < c.len()` and `k+2 < c.len()` are the necessary checks. Also, explicitly `assume` `result_len` is non-negative since it's `c_len - m` which can be 0. */
{
    let c_len = c.len();

    if m >= c_len {
        return Vec::new();
    }

    let mut result_vec: Vec<i8> = Vec::new();
    let result_len = c_len - m;
    assume(result_len >= 0);

    if m == 1 {
        let scl_val = scl; // keep as i8

        while result_vec.len() < result_len
            invariant
                0 <= result_vec.len(),
                result_vec.len() <= result_len,
                result_len == c_len - m,
                c_len >= 1,
                m == 1,
                forall|k: int| 0 <= k < result_vec.len() ==> k + 1 < c_len ==> 
                    result_vec[k] as int == scl_val as int * (2 * (k + 1) as int) * (c[k + 1] as int),
            decreases result_len - result_vec.len()
        {
            let i = result_vec.len();
            if (i + 1) as usize >= c_len {
                // This case should not be reached based on the loop invariants and termination conditions
                // However, Verus needs explicit conditions for indexing access
                break;
            }
            let val = (scl_val as i64 * (2 * ((i + 1) as i64)) * (c[i + 1] as i64)) as i8;
            result_vec.push(val);
        }
    } else if m == 2 {
        if c_len < 2 { return Vec::new(); }
        let scl_val = scl; // keep as i8
        let scl_sq_val = (scl as i64 * scl as i64) as i8;

        while result_vec.len() < result_len
            invariant
                0 <= result_vec.len(),
                result_vec.len() <= result_len,
                result_len == c_len - m,
                c_len >= 2,
                m == 2,
                forall|k: int| 0 <= k < result_vec.len() ==> k + 2 < c_len ==> 
                    result_vec[k] as int == 
                    scl_sq_val as int * (2 * (k + 2) as int) * (2 * (k + 1) as int) * (c[k + 2] as int),
            decreases result_len - result_vec.len()
        {
            let i = result_vec.len();
            if (i + 2) as usize >= c_len {
                // This case should not be reached based on the loop invariants and termination conditions
                // However, Verus needs explicit conditions for indexing access
                break;
            }
            let val = (scl_sq_val as i64 * (2 * ((i + 2) as i64)) * (2 * ((i + 1) as i64)) * (c[i + 2] as i64)) as i8;
            result_vec.push(val);
        }
    }
    
    result_vec
}
// </vc-code>

}
fn main() {}