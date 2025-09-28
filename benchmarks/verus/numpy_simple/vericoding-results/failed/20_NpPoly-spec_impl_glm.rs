// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn poly_helper_spec(roots: Seq<f32>, val: nat) -> Seq<f32>;

/* helper modified by LLM (iteration 5): marked as uninterpreted function */
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
    /* code modified by LLM (iteration 5): added decreases clause to while loops */
    let n = roots.len();
    let mut coeffs: Vec<f32> = Vec::new();
    if n > 0 {
        coeffs.push(-roots[0]);
    }
    let mut i = 1;
    while i < n
        invariant
            1 <= i <= n,
            coeffs.len() == i,
        decreases n - i
    {
        let r = roots[i];
        assert(i < roots.len());
        let mut new_coeffs: Vec<f32> = Vec::new();
        assert(0 < coeffs.len());
        new_coeffs.push(coeffs[0] - r);
        let mut j = 1;
        while j < i
            invariant
                1 <= j <= i,
                new_coeffs.len() == j,
            decreases i - j
        {
            assert(j < coeffs.len());
            assert(j-1 < coeffs.len());
            new_coeffs.push(coeffs[j] - r * coeffs[j-1]);
            j += 1;
        }
        new_coeffs.push(-r * coeffs[i-1]);
        coeffs = new_coeffs;
        i += 1;
    }
    coeffs
}
// </vc-code>


}
fn main() {}