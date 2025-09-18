// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): convert usize to int */
spec fn usize_to_int(i: usize) -> int { i as int }
// </vc-helpers>

// <vc-spec>
fn fromfunction(n: usize, f: spec_fn(usize) -> f32) -> (result: Vec<f32>)
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i] == f(i as usize)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement fromfunction with loop and corrected invariant indexing */
    let mut v: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant v.len() == i,
        invariant forall|k: int| 0 <= k && k < (i as int) ==> (v@)[k as usize] == f(k as usize),
        decreases n - i
    {
        v.push(f(i));
        i += 1;
    }
    v
}
// </vc-code>

}
fn main() {}