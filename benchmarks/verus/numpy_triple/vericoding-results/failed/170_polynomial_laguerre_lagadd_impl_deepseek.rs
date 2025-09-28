// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed f32_add_spec to use spec_add instead of + */
proof fn max_usize_spec(a: usize, b: usize) -> (max: usize)
    ensures
        max == max_usize(a, b)
{
    if a >= b {
        a
    } else {
        b
    }
}

proof fn f32_add_spec(a: f32, b: f32) -> (sum: f32)
    ensures
        sum == f32_add(a, b)
{
    a.spec_add(b)
}
// </vc-helpers>

// <vc-spec>
spec fn evaluate_laguerre_polynomial(coeffs: Seq<f32>, x: f32) -> f32
{
    arbitrary()
}

spec fn f32_add(a: f32, b: f32) -> f32
{
    arbitrary()
}

spec fn max_usize(a: usize, b: usize) -> usize
{
    if a >= b { a } else { b }
}

fn lagadd(c1: Vec<f32>, c2: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == max_usize(c1.len(), c2.len()),
        forall|i: int| 0 <= i < result.len() ==> {
            #[trigger] result[i] == f32_add(
                if i < c1.len() { c1[i] } else { 0.0f32 },
                if i < c2.len() { c2[i] } else { 0.0f32 }
            )
        },
        (c1.len() > 0 || c2.len() > 0) ==> result.len() > 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed compilation error by using f32_add_spec helper */
{
    let max_len = if c1.len() >= c2.len() { c1.len() } else { c2.len() };
    let mut result = Vec::new();

    let mut i: usize = 0;
    while i < max_len
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                #[trigger] result[j] == f32_add(
                    if j < c1.len() { c1[j] } else { 0.0f32 },
                    if j < c2.len() { c2[j] } else { 0.0f32 }
                )
            },
            i <= max_len
    {
        let mut sum = 0.0f32;
        proof {
            let a_val = if i < c1.len() { c1[i] } else { 0.0f32 };
            let b_val = if i < c2.len() { c2[i] } else { 0.0f32 };
            f32_add_spec(a_val, b_val);
        }
        if i < c1.len() {
            sum = c1[i];
        }
        if i < c2.len() {
            sum = sum + c2[i];
        }
        result.push(sum);
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}