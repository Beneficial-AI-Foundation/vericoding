// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): clone and push helper */
fn clone_and_push(mut v: Vec<i32>, b: i32) -> Vec<i32> {
    v.push(b);
    v
}
// </vc-helpers>

// <vc-spec>
fn append(a: &Vec<i32>, b: i32) -> (result: Vec<i32>)
    ensures
        result.len() == a.len() + 1,
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i],
        result[a.len() as int] == b,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): clone input vector and push b */
    let mut result: Vec<i32> = a.clone();
    result.push(b);
    result
}
// </vc-code>

}
fn main() {}