// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Adding a body to the spec function vec_sum to define its behavior. */
spec fn vec_sum(a: Seq<f32>) -> f32
{
    if a.len() == 0 {
        0.0f32
    } else {
        a[0] + vec_sum(a.subsequence(1, a.len()))
    }
}
// </vc-helpers>

// <vc-spec>
spec fn vec_sum(a: Seq<f32>) -> f32;

fn sum(a: Vec<f32>) -> (result: f32)
    ensures 
        result == vec_sum(a@),
        a.len() == 0 ==> result == 0.0f32,
        (forall|i: int| 0 <= i < a.len() ==> a[i] == 0.0f32) ==> result == 0.0f32,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type mismatches and added correct index access using `@` for sequences. */
{
    let mut i: int = 0;
    let mut res: f32 = 0.0f32;
    while i < a.len() as int
        invariant
            0 <= i <= a.len() as int,
            res == vec_sum(a@.subsequence(0, i)),
        decreases (a.len() as int) - i
    {
        res = res + a[i as usize];
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}