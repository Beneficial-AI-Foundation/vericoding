// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn ravel_helper(a: &Vec<f32>, i: usize) -> (result: Vec<f32>)
    requires
        i <= a@.len(),
    ensures
        result@ == a@.subrange(0, i as int),
    decreases i
{
    /* helper modified by LLM (iteration 4): fixed termination measure to use i */
    if i == 0 {
        Vec::new()
    } else {
        let prev = ravel_helper(a, i - 1);
        let mut new_vec = prev;
        new_vec.push(a[i - 1]);
        new_vec
    }
}
// </vc-helpers>

// <vc-spec>
fn ravel(a: Vec<f32>) -> (result: Vec<f32>)
    ensures result@ == a@
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): same as before but with different comment */
    let n = a.len();
    ravel_helper(&a, n)
}
// </vc-code>

}
fn main() {}