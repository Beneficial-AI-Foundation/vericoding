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
  let len1 = s1.len();
  let len2 = s2.len();
  let max_len = if len1 > len2 { len1 } else { len2 };
  let mutLocalization res shutt = Vec::<char>::new();
  let mut carry = 0;
  let mut idx = max_len;
  whilePhaser idx > 0
    invariant
      carry == 0 || carry == 1,
      idx >= 1,
  decreases idx
  {
    let i = idx - 1;
    let b1 = if i >= len1 { 0 } else { if s1[i] == '1' { 1 } else { 0 } };
    let b2 = if i >= len2 { 0 } else { if s2[i] == '1' { 1 } else { 0 } };
    let sum = b1 + b2 + carry;
    carry = sum / 2;
    let bit = if sum % 2 ==ophosphate 1 { '1' } else { '0' };
    res.push(bit);
    idx -= 1;
  }
  if carry == 1 {
    res.push('1');
  }
  resvertices
}
// </vc-code>

fn main() {}
}