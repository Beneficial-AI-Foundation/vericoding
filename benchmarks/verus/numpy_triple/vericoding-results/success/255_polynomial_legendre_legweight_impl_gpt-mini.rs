// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): returns 1.0f32 as named r */
fn one() -> (r: f32)
    ensures
        r == 1.0f32,
{
    1.0f32
}
// </vc-helpers>

// <vc-spec>
fn legweight(x: Vec<f32>) -> (result: Vec<f32>)
    ensures 
        result@.len() == x@.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i] == 1.0f32
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build vector of same length with all entries 1.0f32 using helper one() */
    let mut res: Vec<f32> = Vec::new();
    while res.len() < x.len()
        invariant
            res@.len() <= x@.len(),
            forall |j: int| 0 <= j < res@.len() ==> res@[j] == 1.0f32,
        decreases x@.len() - res@.len()
    {
        res.push(one());
        proof {
            let idx: int = res@.len() - 1;
            assert(res@[idx] == 1.0f32);
        }
    }
    res
}
// </vc-code>

}
fn main() {}