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
{ /* code modified by LLM (iteration 3): Fix type error for 'nat' and 'usize' and remove unnecessary casting */
    if s.len() == 0 {
        return None;
    }

    let mut smallest_so_far: nat = s[0];
    let mut i: usize = 1;

    while i < s.len()
        invariant 
            1 <= i as int <= s.len() as int,
            (exists|j: int| 0 <= j < i as int && s[j] == smallest_so_far),
            (forall|j: int| 0 <= j < i as int ==> smallest_so_far <= s[j]),
            smallest_so_far <= s[0],
        decreases s.len() - i
    {
        if s[i] < smallest_so_far {
            smallest_so_far = s[i];
        }
        i = i + 1;
    }
    
    Some(smallest_so_far)
}
// </vc-code>

}
fn main() {}