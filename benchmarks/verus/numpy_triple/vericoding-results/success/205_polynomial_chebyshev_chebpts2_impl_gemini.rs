// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn chebpts2(n: usize) -> (result: Vec<f32>)
    requires n >= 2,
    ensures
        result.len() == n,

        result[0] == -1.0f32,

        result[(n-1) as int] == 1.0f32,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): [use Vec::new and a loop to avoid unsupported vec! macro] */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
        decreases n - i
    {
        result.push(0.0f32);
        i = i + 1;
    }
    result.set(0, -1.0f32);
    result.set(n - 1, 1.0f32);
    result
}
// </vc-code>

}
fn main() {}