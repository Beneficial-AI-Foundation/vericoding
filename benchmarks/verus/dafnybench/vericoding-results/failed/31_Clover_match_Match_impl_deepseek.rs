use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier::trigger]
fn char_match(s_char: char, p_char: char) -> (b: bool)
    ensures b == (s_char == p_char || p_char == '?')
{
    s_char == p_char || p_char == '?'
}

proof fn proof_forall_char_match(s: Seq<char>, p: Seq<char>, n: int) 
    requires 
        s.len() == p.len(),
        0 <= n < s.len(),
        forall|i: int| 0 <= i < s.len() ==> s[i] == p[i] || p[i] == '?'
    ensures 
        char_match(s[n], p[n])
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn match_strings(s: Seq<char>, p: Seq<char>) -> (b: bool)
  requires s.len() == p.len()
  ensures b == (forall|n: int| 0 <= n < s.len() ==> s[n] == p[n] || p[n] == '?')
// </vc-spec>
// <vc-code>
{
  let mut i: usize = 0;
  while i < s.len()
    invariant
        0 <= i <= s.len(),
        forall|n: int| 0 <= n < i ==> s[n] == p[n] || p[n] == '?'
  {
      assert(s[i] == p[i] || p[i] == '?') by {
          proof_forall_char_match(s, p, i as int);
      };
      if !char_match(s[i], p[i]) {
          return false;
      }
      i = i + 1;
  }
  true
}
// </vc-code>

fn main() {
}

}