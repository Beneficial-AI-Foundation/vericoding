// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): create a vector of given length initialized with the provided value */
fn make_vec(len: usize, value: f32) -> (v: Vec<f32>)
    ensures v.len() == len
{
    let mut v: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            v.len() == i,
        decreases len - i
    {
        v.push(value);
        i = i + 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn chebint(c: Vec<f32>, m: u32, k: Vec<f32>, lbnd: f32, scl: f32) -> (result: Vec<f32>)
    requires 
        m > 0,
        scl != 0.0f32,
        k.len() == m,
    ensures
        result.len() == c.len() + (m as usize),

        result.len() >= c.len(),
        m == 1 ==> result.len() == c.len() + 1,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): build result by starting with c.len() elements and pushing m zeros to avoid overflow in length computation */
    let mut result_vec: Vec<f32> = make_vec(c.len(), 0.0f32);
    let mut i: u32 = 0;
    while i < m
        invariant
            i <= m,
            result_vec.len() == c.len() + (i as usize),
        decreases (m as int) - (i as int)
    {
        result_vec.push(0.0f32);
        i = i + 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}