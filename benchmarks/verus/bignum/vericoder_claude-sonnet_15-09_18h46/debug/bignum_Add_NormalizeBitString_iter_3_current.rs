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
    /* code modified by LLM (iteration 3): fixed compilation errors in NormalizeBitString */
    let mut result = Vec::new();
    let mut start_idx = 0;
    
    // Find first non-zero character
    while start_idx < s.len()
        invariant
            start_idx <= s.len(),
    {
        if s[start_idx] == '1' {
            break;
        }
        start_idx += 1;
    }
    
    // If all zeros or empty, return "0"
    if start_idx == s.len() {
        result.push('0');
        return result;
    }
    
    // Copy from first '1' to end
    let mut i = start_idx;
    while i < s.len()
        invariant
            start_idx <= i,
            i <= s.len(),
            ValidBitString(result@),
            result@.len() == i - start_idx,
    {
        result.push(s[i]);
        i += 1;
    }
    
    result
}
// </vc-code>

// <vc-helpers>
/* helpers modified by LLM (iteration 3): fixed type annotations for nat literals */
spec fn power_of_2(n: nat) -> nat
    decreases n
{
    if n == 0 { 1nat } else { 2nat * power_of_2((n - 1) as nat) }
}

spec fn digit_value(c: char, pos: nat) -> nat {
    if c == '1' { power_of_2(pos) } else { 0nat }
}

proof fn str2int_append_lemma(s: Seq<char>, c: char)
    requires ValidBitString(s), c == '0' || c == '1'
    ensures ValidBitString(s.push(c)),
        Str2Int(s.push(c)) == 2 * Str2Int(s) + (if c == '1' { 1nat } else { 0nat })
{
}
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
    /* code modified by LLM (iteration 3): fixed reverse() call to avoid complex arguments */
    let mut result = Vec::new();
    let mut carry = 0u8;
    let mut i1 = s1.len();
    let mut i2 = s2.len();
    
    // Add from right to left
    while i1 > 0 || i2 > 0 || carry > 0
        invariant
            i1 <= s1.len(),
            i2 <= s2.len(),
            carry <= 2,
            ValidBitString(result@),
    {
        let mut sum = carry;
        
        if i1 > 0 {
            i1 -= 1;
            if s1[i1] == '1' {
                sum += 1;
            }
        }
        
        if i2 > 0 {
            i2 -= 1;
            if s2[i2] == '1' {
                sum += 1;
            }
        }
        
        if sum % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        
        carry = sum / 2;
    }
    
    // Reverse the result since we built it backwards
    let mut final_result = Vec::new();
    let mut rev_i = result.len();
    while rev_i > 0
        invariant
            rev_i <= result.len(),
            ValidBitString(final_result@),
    {
        rev_i -= 1;
        final_result.push(result[rev_i]);
    }
    
    // Handle empty result case
    if final_result.len() == 0 {
        final_result.push('0');
    }
    
    final_result
}
// </vc-code>

fn main() {}
}


