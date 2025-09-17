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
    /* code modified by LLM (iteration 6): skip leading zeros only if input is valid bit string, ensure exactly '0' or '1' characters, handle empty string as '0' */
    let mut is_valid = true;
    for &c in s.iter() {
        if c != '0' && c != '1' {
            is_valid = false;
            break;
        }
    }
    let mut result = Vec::<char>::new();
    if is_valid {
        let mut i = 0;
        while i < s.len() && s[i] == '0'
            invariant
                0 <= i <= (s.len() as int),
            decreases
                (s.len() as int - i),
        {
            i += 1;
        }
        if i < s.len() {
            for j in i..s.len() {
                result.push(s[j]);
            }
        } else {
            result.push('0');
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
    /* code modified by LLM (iteration 6): fix compilation error by using usize for loop index to avoid type errors, adjust loop structure for usize */
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
    let mut i: usize = max_len;
    while i > 0
        invariant
            0 <= i <= max_len,
            0 <= result.len() as int <= (max_len as int - i),
            0 <= carry <= 2,
        decreases
            i,
    {
        i -= 1;
        let b1 = if s1_ext[i] == '1' { 1 } else { 0 };
        let b2 = if s2_ext[i] == '1' { 1 } else { 0 };
        let sum = b1 + b2 + carry;
        let bit = sum % 2;
        result.insert(0, if bit == 1 { '1' } else { '0' });
        carry = sum / 2;
    }
    if carry == 1 {
        result.insert(0, '1');
    }
    result
}
// </vc-code>

fn main() {}
}


