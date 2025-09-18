// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added proof function to bridge spec and exec */
proof fn get_f_val(i: usize, f: spec_fn(usize) -> f32) -> (res: f32)
    ensures res == f(i)
{
    f(i)
}
// </vc-helpers>

// <vc-spec>
fn fromfunction(n: usize, f: spec_fn(usize) -> f32) -> (result: Vec<f32>)
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i] == f(i as usize)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): called proof helper to get value from spec_fn */
{
    let mut result = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == f(j as usize),
        decreases n - i
    {
        let val = get_f_val(i, f);
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}