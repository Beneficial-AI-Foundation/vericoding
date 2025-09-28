// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_upper_vowel(c: char) -> bool {
    c == 'A' || c == 'E' || c == 'U' || c == 'I' || c == 'O'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added exec function to check upper vowel in exec mode */
fn is_upper_vowel_exec(c: char) -> (result: bool)
    ensures result == is_upper_vowel(c)
{
    c == 'A' || c == 'E' || c == 'U' || c == 'I' || c == 'O'
}
// </vc-helpers>

// <vc-spec>
fn count_upper(s: Vec<char>) -> (cnt: usize)
    ensures cnt == Set::<int>::new(|i: int| 0 <= i < s@.len() && i % 2 == 0 && is_upper_vowel(s@[i])).len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed count type to usize to match return type */
    let mut count: usize = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            count == Set::<int>::new(|j: int| 0 <= j < i && j % 2 == 0 && is_upper_vowel(s@[j])).len(),
        decreases s.len() - i
    {
        if i % 2 == 0 && is_upper_vowel_exec(s[i]) {
            count = count + 1;
        }
        i += 1;
    }
    count
}
// </vc-code>


}

fn main() {}