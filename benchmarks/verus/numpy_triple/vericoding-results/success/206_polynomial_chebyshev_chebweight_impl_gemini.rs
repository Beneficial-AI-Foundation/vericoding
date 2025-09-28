// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): marked spec_mul as uninterp to fix warning */
uninterp spec fn spec_mul(a: f32, b: f32) -> f32;

/* helper modified by LLM (iteration 4): used external_body for float multiplication wrapper */
#[verifier(external_body)]
fn mul_f32_wrapper(a: f32, b: f32) -> (res: f32)
    ensures res == spec_mul(a, b)
{
    a * b
}

spec fn get_weight_spec(i: int, n: int) -> f32 {
    if i == 0 || i == n - 1 {
        1.0f32
    } else {
        2.0f32
    }
}

fn get_weight(i: usize, n: usize) -> (weight: f32)
    requires
        n > 0,
        i < n,
    ensures
        weight == get_weight_spec(i as int, n as int),
{
    if i == 0 || i == n - 1 {
        1.0f32
    } else {
        2.0f32
    }
}
// </vc-helpers>

// <vc-spec>
fn chebweight(x: Vec<f32>) -> (result: Vec<f32>)
    requires 
        x.len() > 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): no logical change as fix was in helpers */
    let n = x.len();
    let mut result = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            n == x.len(),
            0 <= i <= n,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] result@[k] == spec_mul(x@[k], get_weight_spec(k, n as int)),
        decreases n - i
    {
        let weight = get_weight(i, n);
        let weighted_elem = mul_f32_wrapper(x[i], weight);
        result.push(weighted_elem);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}