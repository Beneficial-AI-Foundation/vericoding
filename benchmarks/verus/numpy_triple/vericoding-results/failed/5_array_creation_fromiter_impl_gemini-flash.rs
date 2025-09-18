// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers to fix */
// </vc-helpers>

// <vc-spec>
fn fromiter<T: Copy>(n: usize, iter: spec_fn(usize) -> T) -> (result: Vec<T>)
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i] == iter(i as usize)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Removed `v.capacity()` check in invariant to fix compilation error due to unsupported `alloc::vec::impl&%1::capacity`. */
{
    let mut v: Vec<T> = Vec::new();
    if n == 0 {
        return v;
    }

    v.reserve(n as usize);

    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            v.len() == i,
            // v.capacity() >= n, // This line was causing a compilation error
            forall|j: int| 0 <= j < i ==> v[j] == iter(j as usize),
    {
        v.push(iter(i));
        i = i + 1;
    }
    v
}
// </vc-code>

}
fn main() {}