// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn cum_prod(a: Vec<i8>) -> (result: Vec<i8>)
    requires a.len() > 0,
    ensures 
        result.len() == a.len(),
        result[0] == a[0],
        forall|i: int| 0 < i < a.len() ==> result[i] as int == result[i-1] as int * a[i] as int
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [Fixing invariant not satisfied for the forall clause during loop iteration. The type casting issues are resolved from the previous iteration. The primary issue now is ensuring the `forall` invariant holds true at step `i` inside the loop body, before `i` is incremented. The invariant was attempting to assert the property for `i` after it had already been incremented, which led to the `forall` failing.] */
{
    let mut result: Vec<i8> = Vec::new();
    result.push(a[0]);

    let mut i: usize = 1;
    while i < a.len()
        invariant
            result.len() == i,
            result[0] == a[0],
            forall|j: int| 0 < j && (j as usize) < i ==> result[j as usize] == result[j as usize - 1] * a[j as usize],
            i > 0,
            i <= a.len(),
        decreases a.len() - i
    {
        // Before updating result, we assert the property for the *current* i.
        // The `forall` in the invariant is for `j < i`, so at each step `i`
        // the loop should ensure the property holds for elements up to `i-1`.
        // The new element is `a[i]` and `result[i] = result[i-1] * a[i]`. After this
        // the invariant for the next step `i+1` will be satisfied.
        result.push(result[i - 1] * a[i]);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}