// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn poly_helper_spec(roots: Seq<f32>) -> (result: Seq<f32>)
    requires
        roots.len() > 0
    ensures
        result.len() == roots.len()
{
    /* helper modified by LLM (iteration 5): Removed duplicate spec function */
    let n = roots.len() as nat;
    let mut result = Seq::empty();
    result = result.push(1.0f32);
    for k in 1..n {
        let new_val = -roots[k - 1] * result[k - 1];
        result = result.push(new_val);
    }
    result
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
/* code modified by LLM (iteration 5): Removed redundant spec function declaration */
{
    let n = roots.len();
    let mut result = Vec::new();
    result.push(1.0f32);
    
    for k in 1..n {
        let prev_val = result[k - 1];
        let new_val = -roots[k - 1] * prev_val;
        result.push(new_val);
    }
    
    result
}
// </vc-code>


}
fn main() {}