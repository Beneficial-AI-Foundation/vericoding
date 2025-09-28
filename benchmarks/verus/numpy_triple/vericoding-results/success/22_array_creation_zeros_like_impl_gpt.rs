// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): additive identity for i32 without triggers */
proof fn lemma_i32_add_zero(x: i32)
    ensures
        x + 0 == x,
        0 + x == x,
{
}

// </vc-helpers>

// <vc-spec>
fn zeros_like(a: &Vec<i32>) -> (result: Vec<i32>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == 0,
        forall|v: &Vec<i32>| v.len() == result.len() ==> {
            forall|i: int| 0 <= i < result.len() ==> 
                result[i] + v[i] == v[i] && v[i] + result[i] == v[i]
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): build a zero-initialized Vec matching a's length using a simple loop */
    let mut res: Vec<i32> = Vec::new();
    while res.len() < a.len()
        invariant
            res.len() <= a.len(),
            forall|j: int| 0 <= j < res.len() ==> res@[j] == 0,
        decreases a.len() - res.len()
    {
        res.push(0);
    }
    res
}
// </vc-code>

}
fn main() {}