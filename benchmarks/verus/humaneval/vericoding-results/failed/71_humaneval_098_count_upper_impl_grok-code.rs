// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_upper_vowel(c: char) -> bool {
    c == 'A' || c == 'E' || c == 'U' || c == 'I' || c == 'O'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes needed */
fn is_upper_vowel_exec(c: char) -> (result: bool)
    ensures is_upper_vowel(c) == result
{
    c == 'A' || c == 'E' || c == 'U' || c == 'I' || c == 'O'
}
// </vc-helpers>

// <vc-spec>
fn count_upper(s: Vec<char>) -> (cnt: usize)
    ensures cnt == Set::<int>::new(|i: int| 0 <= i < s@.len() && i % 2 == 0 && is_upper_vowel(s@[i])).len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type in invariant lambda from nat to int, added lower bound 0 <= j in set predicate */
{
    let mut cnt: usize = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s@.len(),
            cnt == Set::<int>::new(|j: int| 0 <= j < i && j % 2 == 0 && is_upper_vowel(s@[j])).len(),
            0 <= cnt <= s@.len()
        decreases s@.len() - i
    {
        if i % 2 == 0 {
            if is_upper_vowel_exec(s[i]) {
                cnt += 1;
            }
        }
        i += 1;
    }
    cnt
}
// </vc-code>


}

fn main() {}