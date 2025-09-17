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
/* helper modified by LLM (iteration 4): convert char '1'/'0' to nat bit */
spec fn char_bit(c: char) -> nat { if c == '1' { 1nat } else { 0nat } }
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
    /* code modified by LLM (iteration 4): use nat literals and implement binary addition without verification bypass */
    let mut n1: nat = 0nat;
    let mut i: usize = 0usize;
    while i < s1.len()
        invariant
            i <= s1.len(),
        decreases
            s1.len() - i
    {
        let c = s1[i];
        n1 = 2nat * n1 + (if c == '1' { 1nat } else { 0nat });
        i = i + 1;
    }

    let mut n2: nat = 0nat;
    let mut i2: usize = 0usize;
    while i2 < s2.len()
        invariant
            i2 <= s2.len(),
        decreases
            s2.len() - i2
    {
        let c = s2[i2];
        n2 = 2nat * n2 + (if c == '1' { 1nat } else { 0nat });
        i2 = i2 + 1;
    }

    let mut sum: nat = n1 + n2;
    let mut rev = Vec::<char>::new();
    if sum == 0nat {
        return rev;
    }

    while sum > 0nat
        invariant
            sum >= 0nat,
        decreases
            sum
    {
        let ch = if sum % 2nat == 1nat { '1' } else { '0' };
        rev.push(ch);
        sum = sum / 2nat;
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