// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn find_smallest(s: &Vec<nat>) -> (result: Option<nat>)
    ensures
        match result {
            None => s.len() == 0,
            Some(r) => s.len() > 0 && 
                      (exists|i: int| 0 <= i < s.len() && s[i] == r) &&
                      (forall|i: int| 0 <= i < s.len() ==> r <= s[i])
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to while loop */
    if s.len() == 0 {
        return None;
    }
    
    let mut min_val = s[0];
    let mut i = 1;
    
    while i < s.len()
        invariant
            1 <= i <= s.len(),
            forall|j: int| 0 <= j < i ==> min_val <= s[j],
            exists|k: int| 0 <= k < i && s[k] == min_val
        decreases s.len() - i
    {
        if s[i] < min_val {
            min_val = s[i];
        }
        i += 1;
    }
    
    Some(min_val)
}
// </vc-code>

}
fn main() {}