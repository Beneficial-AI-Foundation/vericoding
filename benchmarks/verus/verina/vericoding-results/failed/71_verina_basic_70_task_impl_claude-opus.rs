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
    /* code modified by LLM (iteration 5): Using ghost variable to track spec function result */
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            exists|j: int| i <= j < a.len() && p(a[j]),
            forall|k: int| 0 <= k < i ==> !p(a[k]),
    {
        let ghost found = p(a[i as int]);
        
        if choose|b: bool| b == found {
            assert(p(a[i as int]));
            assert(forall|k: int| 0 <= k < i ==> !p(a[k]));
            return i;
        }
        
        assert(!p(a[i as int]));
        i = i + 1;
    }
    
    unreached()
}
// </vc-code>

}
fn main() {}