// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed placeholder comment as no helpers are needed for this problem. */
// </vc-helpers>

// <vc-spec>
fn element_wise_modulo(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires
        a.len() == b.len(),
        a.len() > 0,
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] % b[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): The type conversion from int to usize in forall clause was causing errors. Changed it back to int. */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i as int,
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j && j < i as int ==> result[j as usize] == a[j as usize] % b[j as usize],
    {
        result.push(a[i] % b[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}