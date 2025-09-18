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
/* code modified by LLM (iteration 2): Changed loop counter 'i' from int to usize to fix compilation errors. */
{
    if s.len() == 0 {
        None
    } else {
        let mut smallest = s[0];
        let mut i: usize = 1;
        while i < s.len()
            invariant
                s.len() > 0,
                1 <= i && i <= s.len(),
                (exists|k: int| 0 <= k < (i as int) && s[k] == smallest),
                (forall|k: int| 0 <= k < (i as int) ==> smallest <= s[k]),
            decreases s.len() - i,
        {
            if s[i] < smallest {
                smallest = s[i];
            }
            i = i + 1;
        }
        Some(smallest)
    }
}
// </vc-code>

}
fn main() {}