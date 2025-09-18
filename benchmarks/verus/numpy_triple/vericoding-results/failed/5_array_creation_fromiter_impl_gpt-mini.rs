// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): cast usize to int */
spec fn usize_to_int(u: usize) -> int { u as int }

/* helper modified by LLM (iteration 5): trivial proof about the cast (helps the verifier) */
proof fn usize_to_int_cast(u: usize) ensures usize_to_int(u) == u as int {
    proof {
        assert(usize_to_int(u) == u as int);
    }
}
// </vc-helpers>

// <vc-spec>
fn fromiter<T: Copy>(n: usize, iter: spec_fn(usize) -> T) -> (result: Vec<T>)
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i] == iter(i as usize)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): build Vec by pushing iter(i) with corrected invariant parentheses */
{
    let mut res: Vec<T> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant res.len() == i
        invariant (forall |k: int| 0 <= k && k < usize_to_int(i) ==> res[k as usize] == iter(k as usize))
        decreases n - i
    {
        res.push(iter(i));
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}