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
    /* code modified by LLM (iteration 5): Build vector iteratively with loop */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == iter(j as usize),
            i <= n,
        decreases n - i
    {
        result.push(iter(i));
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}