// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): spec helper converting usize to int */
spec fn usize_to_int(u: usize) -> int {
    u as int
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
    /* code modified by LLM (iteration 3): clone input vector and push new element */
    let mut res: Vec<i32> = a.clone();
    res.push(b);
    res
}
// </vc-code>

}
fn main() {}