// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed proof/exec mode separation by using exec function properly */
fn fromiter_inner<T: Copy>(i: usize, n: usize, iter: spec_fn(usize) -> T, result: &mut Vec<T>)
    requires
        0 <= i <= n,
        old(result)@.len() == i,
        forall|j: int| 0 <= j < i ==> old(result)@[j] == iter(j as usize),
    ensures
        result@.len() == n,
        forall|j: int| 0 <= j < n ==> result@[j] == iter(j as usize),
    decreases n - i
{
    if i < n {
        let val = iter(i);
        result.push(val);
        fromiter_inner(i + 1, n, iter, result);
    }
}
// </vc-helpers>

// <vc-spec>
fn fromiter<T: Copy>(n: usize, iter: spec_fn(usize) -> T) -> (result: Vec<T>)
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i] == iter(i as usize)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): using corrected fromiter_inner helper */
{
    let mut result = Vec::new();
    fromiter_inner(0, n, iter, &mut result);
    result
}
// </vc-code>

}
fn main() {}