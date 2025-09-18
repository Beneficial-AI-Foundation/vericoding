// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn filled_seq(n: nat, x: f32) -> Seq<f32> { Seq::new(n, |i: int| x) }
// </vc-helpers>

// <vc-spec>
fn numpy_full_like(a: Vec<f32>, fill_value: f32) -> (result: Vec<f32>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == fill_value,
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let mut res: Vec<f32> = Vec::new();
    for i in 0..n
        invariant
            0 <= i <= n,
            res.len() == i,
            forall|j: int| 0 <= j < res.len() ==> res[j] == fill_value
    {
        res.push(fill_value);
    }
    res
}
// </vc-code>

}
fn main() {}