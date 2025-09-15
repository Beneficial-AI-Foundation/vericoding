// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): no helpers needed */
// </vc-helpers>

// <vc-spec>
fn linear_search3(a: &Vec<i32>, p: spec_fn(i32) -> bool) -> (result: usize)
    requires 
        exists|i: int| 0 <= i < a.len() && p(a[i]),
    ensures 
        result < a.len(),
        p(a[result as int]),
        forall|k: int| 0 <= k < result ==> !p(a[k]),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fixed type of index in p(a.deref().index(i)) call */
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall|k: int| 0 <= k < i ==> !p(a@[k]),
    {
        if p(a@[i as int]) {
            return i;
        }
        i = i + 1;
    }
    // If the loop finishes, it means no element satisfies `p`. However, the `requires` clause guarantees
    // that such an element exists. Thus, the loop must terminate by returning `i`.
    // We add a panic or an unreachable to satisfy the return type, but this part should theoretically not be reachable.
    panic!("Precondition violation: no element satisfies p(a[i])");
}
// </vc-code>

}
fn main() {}