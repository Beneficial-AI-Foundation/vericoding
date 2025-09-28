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
fn needs_flipping_exec(c: char) -> bool {
    (c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u') ||
    (c == '1' || c == '3' || c == '5' || c == '7' || c == '9')
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
  requires s@.len() >= 1 && s@.len() <= 50
  ensures result@.len() > 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): add invariants to prove bounds for s[i] */
    let n = s.len();
    let mut result = Vec::new();
    for i in 0..n
        invariant
            i <= n,
            n == s@.len(),
            result@.len() == i,
    {
        let c = s[i];
        if needs_flipping_exec(c) {
            result.push('X');
        } else {
            result.push(c);
        }
    }
    result
}
// </vc-code>


}

fn main() {}