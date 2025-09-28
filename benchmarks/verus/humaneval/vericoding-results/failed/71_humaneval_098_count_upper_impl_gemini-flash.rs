// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_upper_vowel(c: char) -> bool {
    c == 'A' || c == 'E' || c == 'U' || c == 'I' || c == 'O'
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn count_upper(s: Vec<char>) -> (cnt: usize)
    ensures cnt == Set::<int>::new(|i: int| 0 <= i < s@.len() && i % 2 == 0 && is_upper_vowel(s@[i])).len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type of loop variable to avoid casting to int */
    let mut cnt: usize = 0;
    let mut i: usize = 0;

    while i < s.len()
        invariant
            i <= s.len(),
            cnt == Set::<int>::new(|j: int| 0 <= j < i as int && j % 2 == 0 && is_upper_vowel(s@[j])).len(),
        decreases s.len() - i
    {
        if i % 2 == 0 && is_upper_vowel(s@[i as int]) {
            cnt = cnt + 1;
        }
        i = i + 1;
    }
    cnt
}
// </vc-code>


}

fn main() {}