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
/* code modified by LLM (iteration 10): implemented NormalizeBitString logic with validation and leading zero removal */
{
    let mut is_valid = true;
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
        decreases
            s.len() - i,
    {
        if s[i] != '0' && s[i] != '1' {
            is_valid = false;
            break;
        }
        i += 1;
    }
    let mut result = Vec::<char>::new();
    if is_valid {
        let mut start: usize = 0;
        let mut k = start;
        while k < s.len() && s[k] == '0'
            invariant
                0 <= start <= k <= s.len(),
            decreases
                s.len() - k,
        {
            start = k + 1;
            k = start;
        }
        if start == s.len() {
            result.push('0');
        } else {
            k = start;
            while k < s.len()
                invariant
                    0 <= start <= k <= s.len(),
                    0 <= result.len() <= (k - start),
                decreases
                    s.len() - k,
            {
                result.push(s[k]);
                k += 1;
            }
        }
    } else {
        result.push('0');
    }
    proof {
        assert(result.len() > 0);
        if result.len() > 1 {
            assert(result[0] != '0');
        }
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
/* code modified by LLM (iteration 10): fixed compilation error by replacing is_empty with len() == 0 check */
{
    let len1 = s1.len();
    let len2 = s2.len();
    let max_len = if len1 > len2 { len1 } else { len2 };
    let mut s1_ext = Vec::<char>::new();
    let mut idx: usize = 0;
    while idx < (max_len - len1)
        invariant
            0 <= idx <= max_len - len1,
            s1_ext.len() == idx,
        decreases
            max_len - len1 - idx,
    {
        s1_ext.push('0');
        idx += 1;
    }
    s1_ext.extend_from_slice(s1);
    let mut s2_ext = Vec::<char>::new();
    idx = 0;
    while idx < (max_len - len2)
        invariant
            0 <= idx <= max_len - len2,
            s2_ext.len() == idx,
        decreases
            max_len - len2 - idx,
    {
        s2_ext.push('0');
        idx += 1;
    }
    s2_ext.extend_from_slice(s2);
    let mut result = Vec::<char>::new();
    let mut carry = 0;
    let mut i: usize = max_len;
    while i > 0
        invariant
            0 <= i <= max_len,
            0 <= result.len() == (max_len - i),
            0 <= carry <= 2,
            ValidBitString(result@),
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
    if result.len() == 0 {
        result.push('0');
    }
    result
}
// </vc-code>

fn main() {}
}


