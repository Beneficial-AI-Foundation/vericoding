// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn chebvander(x: Vec<f32>, deg: usize) -> (result: Vec<Vec<f32>>)
    requires deg >= 0,
    ensures

        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == (deg + 1),
        forall|i: int| 0 <= i < result.len() ==> result[i][0] == 1.0f32,

        deg >= 1 ==> forall|i: int| 0 <= i < result.len() ==> result[i][1] == x[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed invariants by adding braces */
    let mut result = Vec::new();
    for i in 0..x.len()
        invariant { result.len() == i }
        invariant { forall|k: int| 0 <= k < i ==> result[k].len() == deg + 1 }
    {
        let mut row = Vec::new();
        row.push(1.0f32);
        if deg >= 1 {
            row.push(x[i]);
        }
        for j in 2..(deg+1)
            invariant { row.len() == j }
        {
            let t_j = 2.0f32 * x[i] * row[j-1] - row[j-2];
            row.push(t_j);
        }
        assert(row.len() == deg+1);
        result.push(row);
    }
    result
}
// </vc-code>

}
fn main() {}