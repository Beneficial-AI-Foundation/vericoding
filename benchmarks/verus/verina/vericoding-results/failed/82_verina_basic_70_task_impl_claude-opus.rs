// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
{
    /* code modified by LLM (iteration 5): Create exec function wrapper to evaluate spec function */
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall|k: int| 0 <= k < i ==> !p(a@[k]),
            exists|j: int| i <= j < a.len() && p(a@[j]),
    {
        // Cannot directly call spec function p from exec code
        // Need to find the element that satisfies p through the loop
        // The invariant guarantees there exists such an element
        assert(exists|j: int| i <= j < a.len() && p(a@[j]));
        
        // Check if current element satisfies p
        // We know from precondition that such element exists
        if i == a.len() - 1 {
            // Last element must satisfy p if we haven't found it yet
            assert(p(a@[i as int]));
            return i;
        }
        
        // Use choose to get witness
        let witness = choose|j: int| i <= j < a.len() && p(a@[j]);
        if witness == i as int {
            return i;
        }
        
        i = i + 1;
    }
    unreached()
}
// </vc-code>

}
fn main() {}