use vstd::prelude::*;

verus! {

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else {
    2 * Str2Int(s.subrange(0, s.len() as int - 1))
      + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
  }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  // All characters must be '0' or '1'.
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
proof fn Str2Int_lemma_char_to_nat(c: char) ensures (c == '0' || c == '1') ==> (c == '1' ? 1 nat : 0 nat) == (c as nat - '0' as nat) { }
// </vc-helpers>

// <vc-spec>
exec fn Compare(s1: &[char], s2: &[char]) -> (res: i32)
  requires ValidBitString(s1@),
   ValidBitString(s2@),
  ensures Str2Int(s1@) < Str2Int(s2@) ==> res == -1,
    Str2Int(s1@) == Str2Int(s2@) ==> res == 0,
    Str2Int(s1@) > Str2Int(s2@) ==> res == 1,
  decreases Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): improved comparison logic to handle different lengths and match Str2Int behavior */
{
    let s1_len = s1.len();
    let s2_len = s2.len();

    if s1_len < s2_len {
        return -1;
    } else if s1_len > s2_len {
        return 1;
    }

    // If lengths are equal, lexical comparison from most significant bit
    let mut i = 0;
    while i < s1_len
        invariant 0 <= i <= s1_len,
        invariant ValidBitString(s1@),
        invariant ValidBitString(s2@),
        invariant forall |j: int| 0 <= j < i ==> s1@[j as int] == s2@[j as int],
    {
        let char1 = s1[i];
        let char2 = s2[i];

        if char1 < char2 {
            return -1;
        } else if char1 > char2 {
            return 1;
        }
        i = i + 1;
    }

    return 0;
}
// </vc-code>

fn main() {}
}


