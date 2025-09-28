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
    /* code modified by LLM (iteration 5): use 'choose' to obtain a value satisfying the specification */
    let mut v = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            v.len() == i,
            forall|j: int| 0 <= j < i ==> v@[j] == iter(j as usize),
        decreases n - i
    {
        let item: T = choose|t: T| t == iter(i as usize);
        v.push(item);
        i = i + 1;
    }
    v
}
// </vc-code>

}
fn main() {}