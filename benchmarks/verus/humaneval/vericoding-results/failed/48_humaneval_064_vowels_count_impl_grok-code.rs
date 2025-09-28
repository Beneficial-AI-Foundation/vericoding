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

// </vc-helpers>

// <vc-spec>
fn vowel_count(s: &Vec<char>) -> (count: u8)
  ensures
    count as int >= 0,
    count as int == count_vowels(s@) + (if s@.len() > 0 && s@[s@.len() - 1] == 'y' { 1int } else { 0int })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): used while loop with invariant based on count_vowels to ensure the loop counts vowels correctly */
    let mut count: int = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i as int <= s.len() as int,
            count == count_vowels(s@.subrange(0, i as int))
    {
        if s[i] == 'a' || s[i] == 'e' || s[i] == 'i' || s[i] == 'o' || s[i] == 'u' || 
           s[i] == 'A' || s[i] == 'E' || s[i] == 'I' || s[i] == 'O' || s[i] == 'U' {
            count = count + 1;
        }
        i = i + 1;
    }
    if s.len() > 0 && s[s.len() - 1] == 'y' {
        count = count + 1;
    }
    assert(count >= 0);
    assert(count <= 255);
    count as u8
}
// </vc-code>


}

fn main() {}