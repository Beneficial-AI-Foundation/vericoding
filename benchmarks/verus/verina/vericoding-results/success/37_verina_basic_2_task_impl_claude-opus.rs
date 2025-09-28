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
    /* code modified by LLM (iteration 2): Added decreases clause to while loop */
    if s.len() == 0 {
        return None;
    }
    
    let mut smallest = s[0];
    let mut i: usize = 1;
    
    while i < s.len()
        invariant
            0 < i <= s.len(),
            exists|j: int| 0 <= j < i && s[j] == smallest,
            forall|j: int| 0 <= j < i ==> smallest <= s[j],
        decreases s.len() - i
    {
        if s[i] < smallest {
            smallest = s[i];
        }
        i = i + 1;
    }
    
    Some(smallest)
}
// </vc-code>

}
fn main() {}