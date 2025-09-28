// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn swap_first_and_last_helper(a: Seq<i32>) -> (result: Seq<i32>)
    requires
        a.len() > 0,
    ensures
        result.len() == a.len(),
        result[0] == a[a.len() - 1],
        result[a.len() - 1] == a[0],
        forall|j: int| 1 <= j < a.len() - 1 ==> result[j] == a[j],
{
    /* helper modified by LLM (iteration 5): Seq update method for ghost code */
    let result1 = a.update(0, a[a.len() - 1]);
    let result2 = result1.update(a.len() - 1, a[0]);
    result2
}
// </vc-helpers>

// <vc-spec>
fn swap_first_and_last(a: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() > 0,
    ensures
        result.len() == a.len(),
        result[0] == a[a.len() - 1],
        result[result.len() - 1] == a[0],
        forall|i: int| 1 <= i < result.len() - 1 ==> result[i] == a[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Replace Vec::update with direct index assignment */
    let mut result = a.clone();
    let len = result.len();
    let last_val = result[len - 1];
    let first_val = result[0];
    result[0] = last_val;
    result[len - 1] = first_val;
    result
}
// </vc-code>

}
fn main() {}