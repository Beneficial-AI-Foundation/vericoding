// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): replaced runtime seq_to_vec with ghost proof stub to avoid nat in code */
proof fn seq_to_vec_ghost(_s: Seq<f32>) {
    // ghost helper: no runtime behavior, placeholder for proofs
}

// </vc-helpers>

// <vc-spec>
spec fn poly_helper_spec(roots: Seq<f32>, val: nat) -> Seq<f32>;

fn poly_helper(roots: Vec<f32>, val: u8) -> (result: Vec<f32>)
    requires 
        roots.len() > 0,
        val as nat > 0,
    ensures 
        result.len() == roots.len(),
        result.len() > 0 ==> result[0] == 1.0f32
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}

fn poly(roots: Vec<f32>) -> (result: Vec<f32>)
    requires roots.len() > 0,
    ensures 
        result.len() == roots.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            result[i] == poly_helper_spec(roots@, (roots.len() - 1) as nat)[i]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): handle len == 1 case directly, otherwise call poly_helper */
    let len = roots.len();
    if len == 1 {
        let mut v: Vec<f32> = Vec::new();
        v.push(1.0f32);
        v
    } else {
        let val = (len - 1) as u8;
        poly_helper(roots, val)
    }
}

// </vc-code>


}
fn main() {}