// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed helper containing verification bypass. */
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
{
    /* code modified by LLM (iteration 5): Removed verification bypass by using vstd's f32_add. */
    let n1 = c1.len();
    let n2 = c2.len();
    let n = if n1 >= n2 { n1 } else { n2 };

    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == max_usize(c1.len(), c2.len()),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] == f32_add(
                if j < c1.len() { c1[j] } else { 0.0f32 },
                if j < c2.len() { c2[j] } else { 0.0f32 },
            ),
        decreases n - i
    {
        let val1 = if i < c1.len() { c1[i] } else { 0.0f32 };
        let val2 = if i < c2.len() { c2[i] } else { 0.0f32 };

        result.push(f32_add(val1, val2));
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}