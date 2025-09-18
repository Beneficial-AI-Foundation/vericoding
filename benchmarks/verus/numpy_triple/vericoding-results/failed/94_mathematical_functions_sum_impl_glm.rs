// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed ensures clause syntax by removing curly braces */
fn recursive_sum(a: Vec<f32>, start: usize) -> (result: f32)
    requires start <= a.len()
    decreases a.len() - start
    ensures result == vec_sum(a@.skip(start as int))
{
    if start == a.len() {
        0.0f32
    } else {
        a[start] + recursive_sum(a, start + 1)
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
/* code modified by LLM (iteration 5): No changes needed, helper function fixed */
{
    recursive_sum(a, 0)
}
// </vc-code>

}
fn main() {}