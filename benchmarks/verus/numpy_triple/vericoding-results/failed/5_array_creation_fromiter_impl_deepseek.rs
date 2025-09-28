// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed spec_fn call in ghost code */
fn fromiter_helper_impl<T: Copy>(result: &mut Vec<T>, n: usize, i: usize, iter: impl Fn(usize) -> T)
    requires
        old(result)@.len() == i,
        i <= n,
    ensures
        result@.len() == n,
        forall|j: int| 0 <= j < i ==> result@[j] == old(result)@[j],
        forall|j: int| i <= j < n ==> result@[j] == iter(j as usize)
    decreases n - i
{
    if i < n {
        let value = iter(i);
        result.push(value);
        fromiter_helper_impl(result, n, i + 1, iter);
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
/* code modified by LLM (iteration 5): Use lambda wrapper to handle spec_fn conversion */
{
    let mut result: Vec<T> = Vec::new();
    fromiter_helper_impl(&mut result, n, 0, |i: usize| iter(i));
    result
}
// </vc-code>

}
fn main() {}