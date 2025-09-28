// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [Removed the `#[verifier(pure)]` attribute directly as it was causing a compilation error. The `is_finite` function is inherently pure.] */
#[verifier(external_body)]
fn is_finite(f: f32) -> bool {
    f.is_finite()
}
// </vc-helpers>

// <vc-spec>
fn hermfromroots(roots: Vec<f32>) -> (coef: Vec<f32>)
    ensures
        coef@.len() == roots@.len() + 1,
        roots@.len() > 0 ==> coef@[roots@.len() as int] != 0.0f32
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [Checked `is_finite` for initial coefficients and changed `coef@[0] != 0.0f32` to `coef@[0].is_finite()` in the loop invariants.] */
{
    let l = roots.len();
    if l == 0 {
        let mut coef: Vec<f32> = Vec::new();
        coef.push(1.0f32);
        coef
    } else {
        let mut coef: Vec<f32> = Vec::new();
        coef.push(1.0f32);
        coef.push(-roots.index(0));

        assert(coef@[0].is_finite()); // Ensure initial coefficients are finite
        assert(coef@[1].is_finite());

        let mut i = 1;
        while i < l
            invariant
                0 < i <= l,
                coef@.len() == i + 1,
                forall|j: int| 0 <= j < coef@.len() ==> coef@[j].is_finite(),
                coef@[0].is_finite() // Changed to check if it's finite
            decreases l - i
        {
            let next_root = roots.index(i);
            let mut next_coef: Vec<f32> = Vec::new();
            next_coef.push(coef.index(0));

            let mut j = 0;
            while j < coef.len() - 1
                invariant
                    0 <= j < coef@.len() - 1,
                    next_coef@.len() == j + 1,
                    forall|k: int| 0 <= k < next_coef@.len() ==> next_coef@[k].is_finite(),
                    coef@.len() > 0,
                    next_root.is_finite()
                decreases (coef.len() - 1) - j
            {
                next_coef.push(coef.index(j + 1) - (coef.index(j) * next_root));
                j = j + 1;
            }
            next_coef.push(-coef.index(coef.len() - 1) * next_root);
            coef = next_coef;
            i = i + 1;
        }
        coef
    }
}
// </vc-code>


}
fn main() {}