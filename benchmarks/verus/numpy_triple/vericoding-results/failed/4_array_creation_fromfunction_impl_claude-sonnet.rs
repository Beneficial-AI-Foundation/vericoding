// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed helper function since spec_fn cannot be executed */
// </vc-helpers>

// <vc-spec>
fn fromfunction(n: usize, f: spec_fn(usize) -> f32) -> (result: Vec<f32>)
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i] == f(i as usize)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): directly use spec function f in proof context */
    let mut result = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == f(j as usize)
        decreases n - i
    {
        proof {
            assert(result.len() == i);
        }
        let val = f(i);
        result.push(val);
        i += 1;
        proof {
            assert(result.len() == i);
            assert(result[i as int - 1] == f((i - 1) as usize));
        }
    }
    result
}
// </vc-code>

}
fn main() {}