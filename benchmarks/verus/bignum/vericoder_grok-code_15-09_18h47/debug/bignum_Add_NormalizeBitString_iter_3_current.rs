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

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@),
   t@.len() > 0,
   t@.len() > 1 ==> t@[0] != '0',
   ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): implemented to skip leading zeros, ensure at least one character, and handle edge cases correctly */
    let mut i = 0;
    while i < s.len() && s[i] == '0'
        invariant
            0 <= i <= (s.len() as int),
        decreases
            (s.len() as int - i),
    {
        i += 1;
    }
    let mut result = Vec::<char>::new();
    if i < s.len() {
        for j in i..s.len() {
            result.push(s[j]);
        }
    } else {
        result.push('0');
    }
    result
}
// </vc-code>

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
    /* code modified by LLM (iteration 3): implemented binary addition with carry using while loop instead of for rev to avoid compilation error, with proper invariants */
    let len1 = s1.len();
    let len2 = s2.len();
    let max_len = if len1 > len2 { len1 } else { len2 };
    let mut s1_ext = Vec::<char>::new();
    for _ in 0..(max_len - len1) {
        s1_ext.push('0');
    }
    s1_ext.extend_from_slice(s1);
    let mut s2_ext = Vec::<char>::new();
    for _ in 0..(max_len - len2) {
        s2_ext.push('0');
    }
    s2_ext.extend_from_slice(s2);
    let mut result = Vec::<char>::new();
    let mut carry = 0;
    let mut i = max_len as int - 1;
    while i >= 0
        invariant
            -1 <= i < max_len as int,
            result.len() as int == max_len as int - 1 - i,
            carry == 0 || carry == 1,
        decreases i,
    {
        let b1 = if s1_ext[i as usize] == '1' { 1 } else { 0 };
        let b2 = if s2_ext[i as usize] == '1' { 1 } else { 0 };
        let sum = b1 + b2 + carry;
        let bit = sum % 2;
        result.insert(0, if bit == 1 { '1' } else { '0' });
        carry = sum / 2;
        i -= 1;
    }
    if carry == 1 {
        result.insert(0, '1');
    }
    result
}
// </vc-code>

fn main() {}
}


