// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed compilation error by removing semicolon from if condition. */
spec fn poly_helper_spec(roots: Seq<f32>, val: nat) -> Seq<f32>
{
    if val == 1 {
        let mut result_seq = Seq::<f32>::new(roots.len(), |i: int| 0.0f32);
        result_seq = result_seq.update(0, 1.0f32);
        result_seq
    } else {
        let prev_coeffs = poly_helper_spec(roots, val - 1);
        let mut current_coeffs = Seq::<f32>::new(roots.len(), |i: int| 0.0f32);

        current_coeffs = current_coeffs.update(0, -roots[val as int - 2] * prev_coeffs[0]);

        forall |idx: int| 1 <= idx && idx < val - 1 ==> {
            current_coeffs = current_coeffs.update(idx, prev_coeffs[idx - 1] - roots[val as int - 2] * prev_coeffs[idx]);
        }

        if val as int - 1 < roots.len() {
            current_coeffs = current_coeffs.update(val as int - 1, prev_coeffs[val as int - 2]);
        }
        current_coeffs
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
/* code modified by LLM (iteration 5): Corrected `current_coeffs` length in invariant and `poly_helper_spec` call to match for the `P(i+1)` polynomial. Also adjusted subsequence start for `poly_helper_spec`. */
{
    let mut result = Vec::new();
    if roots.len() == 0 {
        return result;
    }
    
    let mut current_coeffs = Vec::new();
    current_coeffs.push(1.0f32);

    proof {
        assert(current_coeffs.len() == 1);
    }

    let mut i: nat = 0;
    while i < roots.len()
        invariant
            i <= roots.len(),
            current_coeffs.len() == i as int + 1,
            (i as int) < roots.len() ==> current_coeffs@ == poly_helper_spec(roots@, i + 1)@.subsequence(0, i as int + 1),
            current_coeffs.len() > 0 ==> current_coeffs[0] == poly_helper_spec(roots@, i + 1)[0],
            current_coeffs.len() > 0 ==> current_coeffs[0] == if i==0 {1.0f32} else { -roots[i as int - 1] * poly_helper_spec(roots@, i)[0] },
    {
        let mut next_coeffs = Vec::new();
        
        // The coefficient of x^0 in P_{i+1}(x) is (-r_i) * coeff_of_x^0_in_P_i(x)
        // Which simplifies to -r_i since coeff_of_x^0 is 1.0 for P_i(x)
        next_coeffs.push(-roots[i as int] * current_coeffs[0]);

        // Coefficient of x^k (for 1 <= k <= i) in P_{i+1}(x) is:
        // coeff_of_x^{k-1}_in_P_i(x) - r_i * coeff_of_x^k_in_P_i(x)
        let mut k = 1;
        while k < current_coeffs.len()
            invariant
                k <= current_coeffs.len(),
                next_coeffs.len() == k,
                current_coeffs.len() == i as int + 1,
                i <= roots.len(),
                forall |j: int| 0 <= j < k ==> next_coeffs@[j] == {
                    if j == 0 {
                        -roots[i as int] * current_coeffs@[0]
                    } else {
                        current_coeffs@[j - 1] - roots[i as int] * current_coeffs@[j]
                    }
                },
        {
            next_coeffs.push(current_coeffs[k - 1] - roots[i as int] * current_coeffs[k]);
            k = k + 1;
        }

        // Coefficient of x^{i+1} in P_{i+1}(x) is coeff_of_x^i_in_P_i(x)
        if (i as int + 1) < roots.len() + 1 {
            next_coeffs.push(current_coeffs[k - 1]);
        }

        proof {
            assert(next_coeffs.len() == (i + 1) as int + 1);
            assert((i + 1) as int < roots.len() ==> next_coeffs@ == poly_helper_spec(roots@, i + 2)@.subsequence(0, (i + 1) as int + 1));
        }
        current_coeffs = next_coeffs;
        i = i + 1;
    }

    result = current_coeffs;
    result
}
// </vc-code>


}
fn main() {}