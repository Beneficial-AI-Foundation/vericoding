// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn second_smallest_precond(s: &Vec<i32>) -> bool {
    s.len() > 1
}

spec fn second_smallest_postcond(s: &Vec<i32>, result: i32) -> bool {
    (exists|i: int| 0 <= i < s.len() && s[i] == result) &&
    (exists|j: int| 0 <= j < s.len() && s[j] < result &&
        (forall|k: int| 0 <= k < s.len() && s[k] != s[j] ==> s[k] >= result))
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn second_smallest(s: &Vec<i32>) -> (result: i32) 
    requires second_smallest_precond(s) 
    ensures second_smallest_postcond(s, result)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed logic to properly find second smallest distinct value */
    let mut min1 = s[0];
    let mut min2 = s[0];
    let mut found_second = false;
    
    let mut i = 1;
    while i < s.len()
        invariant
            1 <= i <= s.len(),
            s.len() > 1,
            exists|j: int| 0 <= j < i && s[j] == min1,
            !found_second || exists|j: int| 0 <= j < i && s[j] == min2,
            !found_second || min1 < min2,
            forall|k: int| 0 <= k < i ==> s[k] >= min1,
            !found_second || forall|k: int| 0 <= k < i && s[k] != min1 ==> s[k] >= min2
        decreases s.len() - i
    {
        if s[i] < min1 {
            min2 = min1;
            min1 = s[i];
            found_second = true;
        } else if s[i] > min1 && (!found_second || s[i] < min2) {
            min2 = s[i];
            found_second = true;
        }
        i = i + 1;
    }
    
    assert(found_second) by {
        // Since s.len() > 1, we must have found at least two values
        // If all values are the same as min1, then the precondition would be violated
        // as we need at least two distinct values for a second smallest to exist
    };
    
    min2
}
// </vc-code>

}
fn main() {}