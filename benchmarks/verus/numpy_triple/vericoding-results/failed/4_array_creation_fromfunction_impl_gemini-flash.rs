// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Adding wrapper to allow spec_fn call from exec. */
pure fn call_spec_f(f: spec_fn(usize) -> f32, i: usize) -> f32 { f(i) }
// </vc-helpers>

// <vc-spec>
fn fromfunction(n: usize, f: spec_fn(usize) -> f32) -> (result: Vec<f32>)
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i] == f(i as usize)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Calling `call_spec_f` instead of `f` directly to allow spec_fn call from exec. */
{
    let mut v: Vec<f32> = Vec::new();
    v.reserve(n);
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i && i <= n,
            v.len() == i,
            forall|j: int| 0 <= j < i ==> v[j] == f(j as usize),
    {
        v.push(call_spec_f(f, i as usize));
        i = i + 1;
    }
    v
}
// </vc-code>

}
fn main() {}