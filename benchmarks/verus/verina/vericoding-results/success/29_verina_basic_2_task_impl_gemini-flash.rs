// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn min(a: nat, b: nat) -> nat {
    if a < b { a } else { b }
}
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
    if s.len() == 0 {
        None
    } else {
        let mut smallest = s[0];
        let mut i = 1;
        while i < s.len()
            invariant
                0 < s.len(),
                0 <= i,
                i <= s.len(),
                smallest == s[0] || (exists|k: int| 0 <= k < i && smallest == s[k]),
                // smallest value seen so far up to index i-1
                forall|k: int| 0 <= k < i ==> smallest <= s[k],
            decreases s.len() - i
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