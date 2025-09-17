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
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
    requires ValidBitString(s1@), ValidBitString(s2@)
    ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
{
    let mut result = Vec::new();
    let mut carry = 0;
    let mut i = 0;
    let len1 = s1.len();
    let len2 = s2.len();
    let max_len = if len1 > len2 { len1 } else { len2 };
    
    while i <= max_len
        invariant
            ValidBitString(result@),
            carry == 0 || carry == 1,
            i <= max_len + 1
    {
        let bit1 = if i < len1 { if s1[len1 - 1 - i] == '1' { 1 } else { 0 } } else { 0 };
        let bit2 = if i < len2 { if s2[len2 - 1 - i] == '1' { 1 } else { 0 } } else { 0 };
        
        let sum = bit1 + bit2 + carry;
        let result_bit = sum % 2;
        carry = sum / 2;
        
        if i < max_len || carry == 1 {
            result.push(if result_bit == 1 { '1' } else { '0' });
        }
        
        if i == max_len && carry == 0 {
            break;
        }
        
        i += 1;
    }
    
    result.reverse();
    if result.is_empty() {
        result.push('0');
    }
    
    result
}

fn Int2Str(n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n
{
    if n == 0 {
        let mut result = Vec::new();
        result.push('0');
        return result;
    }
    
    let mut result = Vec::new();
    let mut temp = n;
    
    while temp > 0
        invariant ValidBitString(result@)
        decreases temp
    {
        if temp % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        temp = temp / 2;
    }
    
    result.reverse();
    result
}
// </vc-helpers>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    if s1.is_empty() || s2.is_empty() {
        let mut result = Vec::new();
        result.push('0');
        return result;
    }
    
    if (s1.len() == 1 && s1[0] == '0') || (s2.len() == 1 && s2[0] == '0') {
        let mut result = Vec::new();
        result.push('0');
        return result;
    }
    
    let mut result = Vec::new();
    result.push('0');
    
    let mut i = 0;
    while i < s1.len()
        invariant
            ValidBitString(result@),
            i <= s1.len()
    {
        if s1[s1.len() - 1 - i] == '1' {
            let mut shifted_s2 = Vec::new();
            
            let mut j = 0;
            while j < s2.len()
                invariant j <= s2.len()
            {
                shifted_s2.push(s2[j]);
                j += 1;
            }
            
            let mut k = 0;
            while k < i
                invariant k <= i
            {
                shifted_s2.push('0');
                k += 1;
            }
            
            result = Add(&result, &shifted_s2);
        }
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}


