// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn poly_helper_func(coeffs: Seq<f32>, root: f32) -> Seq<f32>
{
    Seq::new(coeffs.len(), |i: int|
        if i == 0 {
            coeffs[0]
        } else {
            coeffs[i] - root * coeffs[i-1]
        }
    )
}

#[verifier::spinoff_prover]
pub proof fn lemma_poly_spec_zeroth(roots: Seq<f32>, val: nat)
    requires
        val < roots.len(),
        roots.len() > 0,
    ensures
        poly_helper_spec(roots, val)[0] == 1.0f32,
    decreases val,
{
    if val > 0 {
        lemma_poly_spec_zeroth(roots, (val - 1) as nat);
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_poly_spec_recursion(roots: Seq<f32>, val: nat)
    requires
        val > 0,
        val < roots.len(),
        roots.len() > 0,
    ensures
        poly_helper_spec(roots, val) == poly_helper_func(poly_helper_spec(roots, (val - 1) as nat), roots[val]),
{
    assert_by_ext_equality(
        poly_helper_spec(roots, val),
        poly_helper_func(poly_helper_spec(roots, (val - 1) as nat), roots[val])
    );
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
    let n = roots.len();

    if n == 1 {
        let mut v = Vec::new();
        v.push(1.0f32);
        proof {
            let spec_res = poly_helper_spec(roots@, 0);
            assert_by_ext_equality(v@, spec_res);
        }
        return v;
    }

    let val_u8 = (n - 1) as u8;
    let res = poly_helper(roots, val_u8);

    proof {
        let val = (n - 1) as nat;
        lemma_poly_spec_recursion(roots@, val);
        let prev_coeffs = poly_helper_spec(roots@, val - 1);
        let result_spec = poly_helper_func(prev_coeffs, roots[val]);
        assert(poly_helper_spec(roots@, val) == result_spec);
    }

    res
}

// </vc-code>


}
fn main() {}