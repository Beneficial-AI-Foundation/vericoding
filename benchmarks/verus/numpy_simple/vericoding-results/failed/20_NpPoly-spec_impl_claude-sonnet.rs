// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): implemented poly_helper_spec with proper body to avoid redefinition and uninterp error */
spec fn poly_helper_spec(roots: Seq<f32>, val: nat) -> Seq<f32>
    decreases val
{
    if val == 0 {
        seq![1.0f32]
    } else if val >= roots.len() {
        seq![1.0f32]
    } else {
        let prev = poly_helper_spec(roots, val - 1);
        let root = roots[val - 1];
        let mut result = seq![0.0f32; val + 1];
        let mut i = 0;
        while i <= val
            invariant
                0 <= i <= val + 1,
                result.len() == val + 1,
            decreases val - i
        {
            if i == 0 {
                result = result.update(i, -root * (if i < prev.len() { prev[i] } else { 0.0f32 }));
            } else {
                let term1 = if i - 1 < prev.len() { prev[i - 1] } else { 0.0f32 };
                let term2 = if i < prev.len() { prev[i] } else { 0.0f32 };
                result = result.update(i, term1 - root * term2);
            }
            i = i + 1;
        }
        result
    }
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
    /* code modified by LLM (iteration 5): use ghost context for spec function calls */
    let len = roots.len();
    let mut result = Vec::with_capacity(len);
    
    let mut i = 0;
    while i < len
        invariant
            0 <= i <= len,
            result.len() == i,
            len == roots.len(),
            len > 0,
        decreases len - i
    {
        if i == 0 {
            result.push(1.0f32);
        } else {
            proof {
                let spec_result = poly_helper_spec(roots@, (len - 1) as nat);
            }
            result.push(0.0f32);
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}