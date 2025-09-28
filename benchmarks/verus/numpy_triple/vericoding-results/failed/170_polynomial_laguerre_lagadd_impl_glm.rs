// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added executable f32_add_exec */
exec fn f32_add_exec(a: f32, b: f32) -> f32 {
    a + b
}
/* helper modified by LLM (iteration 5): added max_usize_exec */
exec fn max_usize_exec(a: usize, b: usize) -> usize {
    if a >= b { a } else { b }
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
{
    /* code modified by LLM (iteration 5): fixed missing max_usize_exec by defining it in helpers */
    let max_len = max_usize_exec(c1.len(), c2.len());
    let mut result = Vec::with_capacity(max_len);
    let mut i = 0;
    
    while i < max_len
        invariant
            0 <= i <= max_len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                #[trigger] result[j] == f32_add(
                    if j < c1.len() { c1[j] } else { 0.0f32 },
                    if j < c2.len() { c2[j] } else { 0.0f32 }
                )
            },
            (c1.len() > 0 || c2.len() > 0) ==> max_len > 0
        decreases max_len - i
    {
        let val1 = if i < c1.len() { c1[i] } else { 0.0f32 };
        let val2 = if i < c2.len() { c2[i] } else { 0.0f32 };
        let sum = f32_add_exec(val1, val2);
        result.push(sum);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}