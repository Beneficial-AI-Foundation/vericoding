// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn replace_at_helper(a: Seq<i32>, j: int, val: i32) -> (result: Seq<i32>)
    requires 0 <= j < a.len()
    ensures
        result.len() == a.len(),
        result[j] == val,
        forall|k: int| 0 <= k < a.len() && k != j ==> result[k] == a[k]
{
    a.update(j, val)
}
// </vc-helpers>

// <vc-spec>
fn test_array_elements(a: &Vec<i32>, j: usize) -> (result: Vec<i32>)
    requires j < a.len(),
    ensures
        result.len() == a.len(),
        result[j as int] == 60,
        forall|k: int| 0 <= k < a.len() && k != j ==> result[k] == a[k],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fix type conversion and ghost/int separation */
    let mut result = a.clone();
    let j_usize: usize = j;
    result[j_usize] = 60;
    result
}
// </vc-code>

}
fn main() {}