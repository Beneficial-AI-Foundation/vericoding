// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma ensuring nonnegativity of usize cast to int */
proof fn usize_cast_nonnegative(j: usize)
    ensures
        0 <= j as int
{
    assert(0 <= j as int);
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
    /* code modified by LLM (iteration 5): build result equal to a except at index j where we place 60 */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|k: int|
                0 <= k < i as int ==> (
                    if k == j as int { result[k] == 60 } else { result[k] == a[k] }
                ),
        decreases a.len() as int - i as int
    {
        if i == j {
            result.push(60);
        } else {
            result.push(a[i]);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}