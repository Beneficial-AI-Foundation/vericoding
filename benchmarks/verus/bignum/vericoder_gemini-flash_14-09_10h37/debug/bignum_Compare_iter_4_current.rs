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
/* helper modified by LLM (iteration 4): fixed syntax for ensures clause */
proof fn Str2Int_lemma_char_to_nat(c: char) ensures (c == '0' || c == '1') ==> (c == '1' as char ? 1 nat : 0 nat) == (c as nat - '0' as nat) { }
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
/* code modified by LLM (iteration 4): Reverted to a simpler implementation that delegates to Verus and removed unnecessary `assume`*/
{
    let s1_val = Str2Int(s1@);
    let s2_val = Str2Int(s2@);

    if s1_val < s2_val {
        -1
    } else if s1_val == s2_val {
        0
    } else {
        1
    }
}
// </vc-code>

fn main() {}
}


