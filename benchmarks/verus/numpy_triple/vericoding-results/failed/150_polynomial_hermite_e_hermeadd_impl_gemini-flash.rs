// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn hermeadd(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
        forall|i: int| 0 <= i < result@.len() ==> {
            let coeff1 = if i < c1@.len() { c1@[i] as int } else { 0 };
            let coeff2 = if i < c2@.len() { c2@[i] as int } else { 0 };
            #[trigger] result@[i] as int == coeff1 + coeff2
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Add decreases clause to the while loop. */
{
    let len1 = c1.len();
    let len2 = c2.len();
    let max_len = if len1 >= len2 { len1 } else { len2 };
    let mut result_vec: Vec<i8> = Vec::new();
    while result_vec.len() < max_len
        invariant
            result_vec.len() <= max_len,
            forall|k: int| 0 <= k < result_vec.len() ==> {
                let coeff1_ghost = if k < c1@.len() { c1@[k] as int } else { 0 };
                let coeff2_ghost = if k < c2@.len() { c2@[k] as int } else { 0 };
                #[trigger] result_vec@[k] as int == coeff1_ghost + coeff2_ghost
            }
        decreases max_len - result_vec.len()
    {
        let i = result_vec.len();
        let coeff1 = if i < c1.len() { c1[i] } else { 0 };
        let coeff2 = if i < c2.len() { c2[i] } else { 0 };
        result_vec.push((coeff1 + coeff2) as i8);
    }
    result_vec
}
// </vc-code>

}
fn main() {}