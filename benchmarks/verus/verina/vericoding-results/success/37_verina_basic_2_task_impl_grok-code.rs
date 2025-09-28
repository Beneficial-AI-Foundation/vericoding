// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): No changes */

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
    /* code modified by LLM (iteration 4): Fixed incorrect use of view() method and changed quantifier indices to int for type consistency */
    if s.len() == 0 {
        None
    } else {
        let mut min: nat = s[0];
        let mut i: usize = 1;
        while i < s.len()
            invariant
                1 <= i <= s.len(),
                0 < s.len(),
                forall |j: int| 0 <= j < i ==> min <= s@[j],
                exists |j: int| 0 <= j < i && s@[j] == min,
            decreases s.len() - i
        {
            if s[i] < min {
                min = s[i];
            }
            i += 1;
        }
        Some(min)
    }
}
// </vc-code>

}
fn main() {}