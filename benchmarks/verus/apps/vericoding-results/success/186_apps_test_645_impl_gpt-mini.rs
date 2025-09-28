// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn is_vowel(c: char) -> bool {
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'
}

spec fn is_odd_digit(c: char) -> bool {
  c == '1' || c == '3' || c == '5' || c == '7' || c == '9'
}

spec fn needs_flipping(c: char) -> bool {
  is_vowel(c) || is_odd_digit(c)
}

spec fn count_flips(s: Seq<char>) -> int {
  s.filter(|c: char| needs_flipping(c)).len() as int
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): proves count_flips is at most the sequence length */
proof fn count_flips_le_len(s: Seq<char>)
    ensures
        count_flips(s) <= s.len() as int,
{
    assert(count_flips(s) == s.filter(|c: char| needs_flipping(c)).len() as int);
    assert(s.filter(|c: char| needs_flipping(c)).len() <= s.len());
    assert((s.filter(|c: char| needs_flipping(c)).len() as int) <= s.len() as int);
    assert(count_flips(s) <= s.len() as int);
}

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
  requires s@.len() >= 1 && s@.len() <= 50
  ensures result@.len() > 0
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 3): return the input vector unchanged */
    let result = s;
    result
}

// </vc-code>


}

fn main() {}