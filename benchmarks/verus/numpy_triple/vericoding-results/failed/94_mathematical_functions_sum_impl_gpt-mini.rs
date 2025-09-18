// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): recursive definition of vec_sum over Seq */
spec fn vec_sum(s: Seq<f32>) -> f32 { if s.len() == 0 { 0.0f32 } else { s@[0] + vec_sum(s[1..]) } }
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
{
    /* code modified by LLM (iteration 5): iterative sum with loop invariants and decreases */
    let s = a@;
    let mut i: nat = 0;
    let mut acc: f32 = 0.0f32;
    while i < a.len()
        invariant i <= a.len()
        invariant acc == vec_sum(s[..i])
        decreases a.len() - i
    {
        acc = acc + s@[i as int];
        i = i + 1;
    }
    acc
}
// </vc-code>

}
fn main() {}