// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added a helper function to correctly define verus_abs_f32_lt. */
fn verus_abs_f32_lt(a: f32, b: f32) -> bool {
    a.abs() < b
}
// </vc-helpers>

// <vc-spec>
fn trimcoef(c: Vec<f32>, tol: f32) -> (result: Vec<f32>)
    ensures
        result.len() >= 1,
        result.len() <= c.len(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected the missing function `verus_abs_f32_lt` by defining it in the helper section. */
{
    let mut idx: usize = c.len() - 1;

    if c.len() == 0 {
        return Vec::new_with(1, |i| 0.0f32);
    }

    while idx > 0 && verus_abs_f32_lt(c@[idx], tol)
        invariant
            0 <= idx,
            idx < c.len(),
            forall |j: int| (idx as int) < j && j < c.len() as int ==> verus_abs_f32_lt(c@[j as usize], tol),
        decreases idx
    {
        idx = idx - 1;
    }

    let final_len: usize = if idx == 0 && verus_abs_f32_lt(c@[0], tol) { 1 } else { idx + 1 };

    let mut result = Vec::new();
    let mut k: usize = 0;
    while k < final_len
        invariant
            0 <= k,
            k <= final_len,
            final_len >= 1,
            result.len() == k,
            forall |j: int| 0 <= j && j < k as int ==> result@[j as usize] == c@[j as usize],
        decreases final_len - k
    {
        result.push(c@[k]);
        k = k + 1;
    }

    result
}
// </vc-code>

}
fn main() {}