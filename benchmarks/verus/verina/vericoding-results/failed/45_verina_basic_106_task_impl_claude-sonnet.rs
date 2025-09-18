// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): helper to prove bounds for vector indexing */
fn bounds_check_helper(i: usize, len: usize)
    requires i < len
    ensures i as int < len as int
{
    assert(i < len);
}
// </vc-helpers>

// <vc-spec>
fn array_sum(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() == b.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i] + b[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added bounds checks and cast i to int in invariant */
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result[j as int] == a[j as int] + b[j as int]
        decreases a.len() - i
    {
        assert(i < a.len());
        assert(i < b.len());
        result.push(a[i] + b[i]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}