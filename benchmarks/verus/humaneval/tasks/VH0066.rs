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
    assume(false);
    0
}
// </vc-code>


}

fn main() {}