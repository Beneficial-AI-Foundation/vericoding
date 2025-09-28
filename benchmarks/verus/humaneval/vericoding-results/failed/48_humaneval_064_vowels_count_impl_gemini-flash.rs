// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_vowel(c: char) -> bool
{
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}

spec fn count_vowels(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0int
    } else {
        count_vowels(s.subrange(1, s.len() as int)) + (if is_vowel(s[0]) { 1int } else { 0int })
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): helper function to check if a char is a vowel in an executable context */
fn is_vowel_exec(c: char) -> bool
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U' || c == 'y'
}
// </vc-helpers>

// <vc-spec>
fn vowel_count(s: &Vec<char>) -> (count: u8)
  ensures
    count as int >= 0,
    count as int == count_vowels(s@) + (if s@.len() > 0 && s@[s@.len() - 1] == 'y' { 1int } else { 0int })
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): implements vowel counting with a loop and handles 'y' as a vowel if it's not the last char */
{
    let mut count: u8 = 0;
    let mut i: usize = 0;

    while i < s.len()
        invariant
            i <= s.len(),
            count as int == count_vowels(s@.subrange(0, i as int)),
            count as int <= s.len() as int,
            count as int >= 0,
        decreases s.len() - i
    {
        if i < s.len() - 1 && is_vowel_exec(s[i]) {
            count = count + 1;
        } else if i == s.len() - 1 && is_vowel(s[i]) { // 'y' is handled in post-condition for last char
            count = count + 1;
        }
        i = i + 1;
    }
    count
}
// </vc-code>


}

fn main() {}