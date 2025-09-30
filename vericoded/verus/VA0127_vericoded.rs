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
proof fn lemma_len_pos(v: Seq<char>)
    requires
        v.len() >= 1,
    ensures
        v.len() > 0,
{
}

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
  requires s@.len() >= 1 && s@.len() <= 50
  ensures result@.len() > 0
// </vc-spec>
// <vc-code>
{
    proof { lemma_len_pos(s@); }
    s
}
// </vc-code>


}

fn main() {}