use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn all_elements_equal(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s[i] == s[j]
}
// </vc-helpers>

// <vc-description>
/*
function_signature: "fn has_only_one_distinct_element(a: &[i32]) -> (result: bool)"
docstring: Implement has only one distinct element functionality.
*/
// </vc-description>

// <vc-spec>
fn has_only_one_distinct_element(a: &[i32]) -> (result: bool)
    ensures result <==> (a.len() > 0 ==> all_elements_equal(a@))
// </vc-spec>

// <vc-code>
{
    if a.len() == 0 {
        return true;
    }
    
    let first = a[0];
    let mut i = 1;
    
    /* code modified by LLM (iteration 4): establish connection between first and a@[0] */
    proof {
        assert(first == a@[0]);
    }
    
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            first == a@[0],
            forall|k: int| 0 <= k < i ==> a@[k] == first
        decreases a.len() - i
    {
        if a[i] != first {
            /* code modified by LLM (iteration 4): fixed proof block with proper connection */
            proof {
                assert(a@[0] == first);
                assert(a@[i as int] != first);
                assert(!all_elements_equal(a@));
            }
            return false;
        }
        i += 1;
    }
    
    proof {
        assert(forall|j: int, k: int| 0 <= j < a@.len() && 0 <= k < a@.len() ==> a@[j] == first && a@[k] == first);
        assert(all_elements_equal(a@));
    }
    
    true
}
// </vc-code>

fn main() {}
}