// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): no helpers needed */
// </vc-helpers>

// <vc-spec>
fn array_split(a: Vec<i32>) -> (ret: (Vec<i32>, Vec<i32>))
    ensures
        a@ == ret.0@ + ret.1@,
        a.len() == ret.0.len() + ret.1.len(),
        a.len() > 1 ==> a.len() > ret.0.len(),
        a.len() > 1 ==> a.len() > ret.1.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Added mid <= len invariant to the first loop to help prove indexing and subrange preconditions. */
    let len = a.len();
    let mid = len / 2;

    let mut left: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < mid
        invariant
            i <= mid,
            a.len() == len,
            mid <= len,
            left@ == a@.subrange(0, i as int),
        decreases mid - i
    {
        left.push(a[i]);
        i = i + 1;
    }

    let mut right: Vec<i32> = Vec::new();
    let mut j: usize = mid;
    while j < len
        invariant
            mid <= j <= len,
            a.len() == len,
            left@ == a@.subrange(0, mid as int),
            right@ == a@.subrange(mid as int, j as int),
        decreases len - j
    {
        right.push(a[j]);
        j = j + 1;
    }

    (left, right)
}
// </vc-code>

}
fn main() {}