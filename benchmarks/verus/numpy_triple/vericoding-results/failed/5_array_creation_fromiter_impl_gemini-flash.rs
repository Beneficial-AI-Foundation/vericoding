// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): remove `spec_fn` from helper to allow execution */
fn iter_exec<T: Copy>(idx: usize, iter: Fn(usize) -> T) -> T {
    iter(idx)
}
// </vc-helpers>

// <vc-spec>
fn fromiter<T: Copy>(n: usize, iter: spec_fn(usize) -> T) -> (result: Vec<T>)
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i] == iter(i as usize)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): adjust closure type for `iter_exec` */
{
    let mut v: Vec<T> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            v.len() == i,
            forall|j: int| 0 <= j < i ==> v[j] == iter(j as usize),
            i <= n,
        decreases n - i
    {
        v.push(iter(i)); // Directly call iter(i) as it's a spec_fn
        i = i + 1;
    }

    v
}
// </vc-code>

}
fn main() {}