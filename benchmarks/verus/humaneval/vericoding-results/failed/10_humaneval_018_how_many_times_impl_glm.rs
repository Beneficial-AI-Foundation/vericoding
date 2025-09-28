// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn is_substring_at(s: &Vec<char>, substr: &Vec<char>, start: usize) -> (result: bool)
    requires start + substr.len() <= s.len()
    ensures result == (s@.subrange(start as int, (start + substr.len()) as int) == substr@)
{
    /* helper modified by LLM (iteration 2): replaced slicing with while loop to fix compilation error */
    let mut i = 0;
    while i < substr.len()
        invariant 
            0 <= i <= substr.len(),
            (forall |j: int| 0 <= j < i ==> s@[(start as int) + j] == substr@[j])
        decreases substr.len() - i
    {
        if s[start + i] != substr[i] {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-helpers>

// <vc-spec>
fn how_many_times(s: Vec<char>, substr: Vec<char>) -> (times: usize)
    ensures times == Set::new(|i: int| 0 <= i <= s@.len() - substr@.len() && s@.subrange(i, i + substr@.len()) == substr@).len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): using fixed helper function */
    let mut count = 0;
    if substr.len() > s.len() {
        return 0;
    }
    let mut i = 0;
    while i <= s.len() - substr.len()
        invariant 
            0 <= i <= s.len() - substr.len() + 1,
            count == Set::new(|j: int| 
                0 <= j < i && 
                s@.subrange(j, j + substr@.len()) == substr@
            ).len(),
        decreases (s.len() - substr.len() + 1) - i
    {
        if is_substring_at(&s, &substr, i) {
            count += 1;
        }
        i += 1;
    }
    count
}
// </vc-code>


}

fn main() {}