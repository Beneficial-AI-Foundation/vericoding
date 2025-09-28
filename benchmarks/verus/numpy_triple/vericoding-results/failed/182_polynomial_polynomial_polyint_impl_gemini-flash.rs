// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The `initial_value_at` function was updated by removing `idx < k.len()` to address a compilation error arising from the inability to directly compare `usize` with `nat`. Instead, the function was refactored to allow `k_seq` as an input parameter, explicitly requiring `Seq` for safety and providing the necessary `idx < k_seq.len()` precondition for access.*/
fn get_new_len(old_len: usize, m: usize) -> (result: usize)
    ensures result == old_len + m
{
    old_len + m
}

fn initial_value_at(k_seq: Seq<i8>, idx: nat) -> i8
    requires
        idx < k_seq.len()
{
    k_seq.index(idx)
}

// </vc-helpers>

// <vc-spec>
fn polyint(c: Vec<i8>, m: usize, k: Vec<i8>, lbnd: i8, scl: i8) -> (result: Vec<i8>)
    requires 
        m > 0 ==> scl as int != 0,
        k.len() == m,
    ensures
        /* Size constraint: output has m more coefficients than input */
        result.len() == c.len() + m,
        
        /* For single integration (m = 1), verify the integration formula */
        m == 1 ==> {
            /* When input is empty polynomial (zero), result is just the constant */
            (c.len() == 0 ==> result@[0] as int == k@[0] as int) &&
            /* For non-empty input, apply integration rules */
            (c.len() > 0 ==> {
                /* Each coefficient c[i] at degree i becomes scl*c[i]/(i+1) at degree i+1 */
                forall|i: int| 0 <= i < c.len() ==> 
                    (i + 1) * (result@[i + 1] as int) == (scl as int) * (c@[i] as int)
            })
        },
        
        /* Property about integration constants and lower bound */
        /* The integration constant is adjusted so that the integral evaluated at lbnd equals k */
        m == 1 && c.len() > 0 ==> {
            /* If we had k = [0] and lbnd = 0, then result[0] = 0 */
            (k@[0] as int == 0 && lbnd as int == 0 ==> result@[0] as int == 0) &&
            /* Example: integrating [1,2,3] with k=3 gives result[0] = 3 when lbnd = 0 */
            (k@[0] as int == 3 && lbnd as int == 0 ==> result@[0] as int == 3)
        },
        
        /* Mathematical property: The integration operation is the inverse of differentiation */
        /* If we integrate m times then differentiate m times, we get back c scaled by scl^m */
        m > 0 && scl as int != 0 ==> true,
        
        /* Sanity check: When scl = 0, all non-constant coefficients become 0 */
        scl as int == 0 ==> forall|i: int| (m as int) <= i < result.len() ==> result@[i] as int == 0,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected two compilation errors that failed verification, by (1) ensuring the j in the while loop is of type `usize` and (2) making current_coeff_seq an @ instead of a Seq<i8> when indexing.*/
{
    let c_len = c.len();
    let new_len = get_new_len(c_len, m);
    let mut result = Vec::new();
    result.reserve(new_len);

    if m > 0 {
        let mut current_coeffs_vec: Vec<i8> = c.clone();

        proof {
            if c_len == 0 && m == 1 {
                assert(c.len() + m == 1);
            }
        }

        let k_seq = k.to_seq();
        let mut i = 0usize;
        while i < m
            invariant
                0 <= i && i <= m,
                current_coeffs_vec.len() == c_len + i,
            decreases m - i
        {
            let mut next_coeffs = Vec::new();
            next_coeffs.push(initial_value_at(k_seq, i as nat));

            let current_coeffs_seq = current_coeffs_vec@;
            let current_coeffs_len = current_coeffs_seq.len();
            let mut j = 0usize;
            while j < current_coeffs_len
                invariant
                    0 <= j && j <= current_coeffs_len,
                    next_coeffs.len() == 1 + j,
                    current_coeffs_seq.len() == current_coeffs_len,
                decreases current_coeffs_len - j
            {
                let coeff_val = current_coeffs_seq.index(j as nat) as i128;
                let j_val = j as i128;
                let scl_val = scl as i128;

                let integrated_coeff;
                if j_val + 1 == 0 {
                    integrated_coeff = 0;
                } else {
                    integrated_coeff = (scl_val * coeff_val) / (j_val + 1);
                }

                next_coeffs.push(integrated_coeff as i8);
                j = j + 1;
            }
            current_coeffs_vec = next_coeffs;
            i = i + 1;
        }
        result = current_coeffs_vec;
    } else {
        result = c.clone();
    }

    result
}
// </vc-code>


}
fn main() {}