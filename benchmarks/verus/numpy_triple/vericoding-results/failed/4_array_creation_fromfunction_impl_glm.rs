// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn fromfunction(n: usize, f: spec_fn(usize) -> f32) -> (result: Vec<f32>)
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i] == f(i as usize)
// </vc-spec>
// <vc-code>
{
    let mut v = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            v.len() == i,
            forall|j: int| 0 <= j < i ==> v[j] == f(j as usize)
    {
        v.push(f(i));
        i += 1;
    }
    v
}
// </vc-code>

}
fn main() {}