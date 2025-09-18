// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn fromiter<T: Copy>(n: usize, iter: spec_fn(usize) -> T) -> (result: Vec<T>)
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i] == iter(i as usize)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement actual loop-based construction without verification bypasses */
    let mut result = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == iter(j as usize)
    {
        result.push(iter(i));
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}