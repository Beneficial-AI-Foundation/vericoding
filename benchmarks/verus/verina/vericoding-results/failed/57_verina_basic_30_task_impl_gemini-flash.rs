// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Fixed loop invariant and assertion for division. */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            result.len() == i,
            i <= a.len(),
            forall|j: int| 0 <= j < i ==> result@[j] == a@[j] % b@[j],
            a.len() == b.len(),
            forall|k: int| 0 <= k < b.len() ==> b@[k] != 0,
        decreases a.len() - i
    {
        // The b[i] != 0 condition is guaranteed by the function's requires clause.
        // We also need to assert that a.len() == b.len() is maintained and that
        // the index i is within bounds for both a and b.
        // The loop condition i < a.len() implicitly handles i < a.len().
        // Since a.len() == b.len() is an invariant, i < a.len() implies i < b.len().
        // No explicit assertion is needed here as the invariant and loop condition cover it.
        result.push(a[i] % b[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}