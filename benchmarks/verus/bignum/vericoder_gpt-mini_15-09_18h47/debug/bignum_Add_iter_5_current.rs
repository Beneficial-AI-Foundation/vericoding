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
/* helper modified by LLM (iteration 5): convert char '1'/'0' to nat bit */
spec fn char_bit(c: char) -> nat { if c == '1' { 1 } else { 0 } }
// </vc-helpers>

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@),
   ValidBitString(s2@),
  ensures ValidBitString(res@), 
    Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute sum via spec Str2Int and convert to binary Vec<char> using loops without nat suffix */
    let mut sum: nat = Str2Int(s1@) + Str2Int(s2@);
    let mut rev = Vec::<char>::new();
    if sum == 0 {
        return rev;
    }

    while sum > 0
        invariant
            sum >= 0,
        decreases
            sum
    {
        let ch = if sum % 2 == 1 { '1' } else { '0' };
        rev.push(ch);
        sum = sum / 2;
    }

    let mut res = Vec::<char>::new();
    let rlen = rev.len();
    let mut j: usize = 0usize;
    while j < rlen
        invariant
            j <= rlen,
        decreases
            rlen - j
    {
        res.push(rev[rlen - 1 - j]);
        j = j + 1;
    }

    res
}
// </vc-code>

fn main() {}
}