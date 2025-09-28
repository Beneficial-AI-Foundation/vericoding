// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed vector indexing bounds and loop invariants */
fn not_equal_impl(x1: Vec<String>, x2: Vec<String>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] != x2[i])
{
    let n = x1.len();
    let mut result = Vec::with_capacity(n);
    let mut i = 0;
    while i < n
        invariant 0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (x1@[j] != x2@[j]),
        decreases n - i
    {
        proof {
            assert(0 <= i < n);
        }
        result.push(x1@[i] != x2@[i]);
        i += 1;
    }
    result
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
/* code modified by LLM (iteration 2): call implementation helper */
{
    not_equal_impl(x1, x2)
}
// </vc-code>

}
fn main() {}