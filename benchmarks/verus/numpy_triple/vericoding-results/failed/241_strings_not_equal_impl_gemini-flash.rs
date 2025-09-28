// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes needed */
fn create_bool_vec(len: usize) -> (result: Vec<bool>)
    ensures result.len() == len
{
    let mut v: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            v.len() == i,
            i <= len,
        decreases len - i
    {
        v.push(false);
        i = i + 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn not_equal(x1: Vec<String>, x2: Vec<String>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] != x2[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected `vec_integral_at` to use `index` method, as the elements are strings not integers. Also corrected the type assertion for `result@[j]` from `int` to `bool` */
{
    let len = x1.len();
    let mut result = create_bool_vec(len as usize);
    let mut i: usize = 0;
    while i < len
        invariant
            result.len() == len,
            x1.len() == len,
            x2.len() == len,
            i <= len,
            forall|j: usize| j < i ==> result@[j] == (x1[j] != x2[j])
        decreases len - i
    {
        result.set(i, x1[i] != x2[i]);
        i = i + 1;
    }
    proof {
        assert forall|idx: int| 0 <= idx && idx < result.len() implies result@[idx] == (x1[idx as usize] != x2[idx as usize]) by {
            assert(idx < i as int);
        }
    }
    result
}
// </vc-code>

}
fn main() {}