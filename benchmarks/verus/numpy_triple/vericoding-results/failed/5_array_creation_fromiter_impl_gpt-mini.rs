// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
{/* helper modified by LLM (iteration 5): prove usize cast to int is non-negative */
fn usize_to_int_nonneg(u: usize)
    ensures
        (u as int) >= 0,
{
    proof {
        assert((u as int) >= 0);
    }
}

/* helper modified by LLM (iteration 5): for non-negative int, casting to usize and back yields the same int */
fn int_nonneg_to_usize_roundtrip(i: int)
    requires
        i >= 0,
    ensures
        (i as usize) as int == i,
{
    proof {
        assert((i as usize) as int == i);
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
{
    /* code modified by LLM (iteration 5): build vector using usize index and spec call without cast */
    let mut res: Vec<T> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            res.len() == i,
            forall|j: int| 0 <= j < i as int ==> res[j as usize] == iter(j as usize),
        decreases
            n - i
    {
        let val: T = spec { iter(i) };
        res.push(val);
        i = i + 1;
    }
    res
}

// </vc-code>

}
fn main() {}