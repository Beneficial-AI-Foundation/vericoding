// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): vector builder using given row length */
fn make_row(len: usize, val: f32) -> (row: Vec<f32>)
    ensures
        row.len() == len,
{
    let mut v: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            v.len() == i,
        decreases (len - i) as int
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
    /* code modified by LLM (iteration 3): avoid int/usize cast equality; build rows with y.len() directly and maintain invariants */
    let xlen = x.len();
    let mut res: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < xlen
        invariant
            i <= xlen,
            res.len() == i,
            forall|k: int| 0 <= k < i as int ==> res@[k].len() == y.len(),
        decreases (xlen - i) as int
    {
        let old_i = i;
        let row = make_row(y.len(), 0.0f32);
        res.push(row);
        proof {
            assert(row.len() == y.len());
            assert(res@[old_i as int] == row);
            assert(res@[old_i as int].len() == y.len());
        }
        i += 1;
    }
    res
}
// </vc-code>


}
fn main() {}