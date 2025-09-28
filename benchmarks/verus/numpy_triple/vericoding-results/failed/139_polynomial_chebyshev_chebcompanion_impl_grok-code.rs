// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn chebcompanion(c: Vec<f32>) -> (result: Vec<Vec<f32>>)
    requires c@.len() >= 2,
    ensures
        result@.len() == c@.len() - 1,
        forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == c@.len() - 1,
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): Fixed invariant syntax by using .len() instead of @.len() for vector lengths */
    let n: usize = c.len();
    let mut inner: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < n - 1
        invariant
            0 <= i <= n - 1,
            inner@.len() == i
        decreases n - 1 - i
    {
        inner.push(0.0);
        i = i + 1;
    }
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut j: usize = 0;
    while j < n - 1
        invariant
            0 <= j <= n - 1,
            result@.len() == j,
            forall |k: int| #![auto] 0 <= k < result@.len() ==> result@[k].len() == n - 1
        decreases n - 1 - j
    {
        result.push(inner.clone());
        j = j + 1;
    }
    result
}
// </vc-code>

}
fn main() {}