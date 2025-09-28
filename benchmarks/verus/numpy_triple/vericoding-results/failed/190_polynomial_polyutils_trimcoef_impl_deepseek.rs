// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type conversion errors and added proper ghost code handling */
fn coeffs_valid(c: Vec<f32>) -> bool {
    c.len() >= 1 &&
    forall|i: int| 0 <= i && i < c.len() as int ==> c[i].is_finite()
}

// Helper function to find the last non-negligible coefficient index
spec fn last_nonzero_index(c: Seq<f32>, tol: f32) -> int
    recommends
        tol >= 0.0f32
    decreases c.len() as int - 0,
{
    if c.len() == 0 {
        -1
    } else if c[c.len() as int - 1].abs() > tol {
        c.len() as int - 1
    } else {
        last_nonzero_index(c.drop_last(1), tol)
    }
}

proof fn last_nonzero_index_lemma(c: Seq<f32>, tol: f32)
    requires
        tol >= 0.0f32,
    ensures
        last_nonzero_index(c, tol) >= -1,
        last_nonzero_index(c, tol) < c.len() as int,
        forall|i: int| last_nonzero_index(c, tol) < i && i < c.len() as int ==> #[trigger] c[i].abs() <= tol,
        last_nonzero_index(c, tol) >= 0 ==> c[last_nonzero_index(c, tol)].abs() > tol
    decreases c.len() as int - 0,
{
    if c.len() == 0 {
        // Base case: empty sequence
    } else if c[c.len() as int - 1].abs() > tol {
        // Base case: last element is non-negligible
    } else {
        // Recursive case: check the rest of the sequence
        last_nonzero_index_lemma(c.drop_last(1), tol);
    }
}
// </vc-helpers>

// <vc-spec>
fn trimcoef(c: Vec<f32>, tol: f32) -> (result: Vec<f32>)
    ensures
        result.len() >= 1,
        result.len() <= c.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type conversion errors and added proper ghost code handling */
    proof {
        last_nonzero_index_lemma(c@, tol);
    }
    
    let n: usize = c.len();
    let mut last_idx: i32 = -1;
    
    // Find the last coefficient with absolute value greater than tolerance
    let mut i: i32 = n as i32 - 1;
    while i >= 0
        invariant
            -1 <= i, i <= n as i32 - 1,
            last_idx >= -1, last_idx <= n as i32 - 1,
            (last_idx >= 0 ==> c[last_idx as usize].abs() > tol),
            forall|j: i32| i < j && j < n as i32 ==> #[trigger] c[j as usize].abs() <= tol
    {
        if c[i as usize].abs() > tol && last_idx == -1 {
            last_idx = i;
        }
        i = i - 1;
    }
    
    // If no coefficients found above tolerance, keep at least one coefficient
    let result_len = if last_idx >= 0 {
        (last_idx as usize) + 1
    } else {
        1
    };
    
    // Create the trimmed vector
    let result = c.truncated(0, result_len);
    
    result
}
// </vc-code>

}
fn main() {}