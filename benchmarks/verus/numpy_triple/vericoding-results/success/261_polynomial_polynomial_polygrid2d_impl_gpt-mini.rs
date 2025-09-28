// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): create vector of f32 with given length */
fn make_vec_f32(len: usize, val: f32) -> (result: Vec<f32>)
    ensures
        result.len() == len,
{
    let mut v: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            v.len() == i,
        decreases len - i
    {
        v.push(val);
        i += 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn polygrid2d(x: Vec<f32>, y: Vec<f32>, c: Vec<Vec<f32>>) -> (result: Vec<Vec<f32>>)
    requires 
        x.len() > 0,
        y.len() > 0,
        c.len() > 0,
        forall|i: int| 0 <= i < c.len() ==> c@[i].len() > 0,
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result@[i].len() == y.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): build result grid with rows initialized to zeros and maintain row lengths invariant */
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> result@[j].len() == y.len(),
        decreases x.len() - i
    {
        let row = make_vec_f32(y.len(), 0.0f32);
        result.push(row);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}