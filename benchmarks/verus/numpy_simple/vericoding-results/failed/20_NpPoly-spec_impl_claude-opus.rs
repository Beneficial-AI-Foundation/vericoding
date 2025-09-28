// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): add uninterp marker to spec function */
#[verifier::uninterp]
spec fn poly_helper_spec(roots: Seq<f32>, val: nat) -> Seq<f32>;
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
    /* code modified by LLM (iteration 4): add decreases clause to loops */
    let mut result = vec![1.0f32];
    let mut val: usize = 1;
    
    while val < roots.len()
        invariant
            val > 0,
            val <= roots.len(),
            result.len() == val,
            result.len() > 0,
            result[0] == 1.0f32,
        decreases roots.len() - val
    {
        let prev = result.clone();
        result = vec![1.0f32];
        
        let mut i: usize = 1;
        while i <= val
            invariant
                i >= 1,
                i <= val + 1,
                result.len() == i,
                result[0] == 1.0f32,
            decreases val + 1 - i
        {
            if i - 1 < prev.len() {
                if i < prev.len() {
                    result.push(prev[i - 1] - roots[val - 1] * prev[i]);
                } else {
                    result.push(prev[i - 1] - roots[val - 1] * 0.0f32);
                }
            } else {
                result.push(0.0f32 - roots[val - 1] * 0.0f32);
            }
            i = i + 1;
        }
        
        val = val + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}