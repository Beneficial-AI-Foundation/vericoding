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
// Helper to add two binary strings
exec fn AddBinary(s1: &[char], s2: &[char]) -> (res: Vec<char>)
    requires ValidBitString(s1@), ValidBitString(s2@)
    ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
{
    let mut result = Vec::new();
    let mut carry = 0u8;
    let mut i = 0;
    
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    
    while i < s1.len() || i < s2.len() || carry > 0
        invariant
            0 <= i <= max_len + 1,
            carry <= 1,
            ValidBitString(result@),
            result@.len() == i,
            Str2Int(result@) + (carry as nat) * pow2(i as nat) == 
                Str2Int(s1@.subrange(0, min(i as int, s1@.len() as int))) + 
                Str2Int(s2@.subrange(0, min(i as int, s2@.len() as int)))
        decreases max_len + 2 - i
    {
        let bit1 = if i < s1.len() {
            if s1[i] == '1' { 1u8 } else { 0u8 }
        } else { 0u8 };
        
        let bit2 = if i < s2.len() {
            if s2[i] == '1' { 1u8 } else { 0u8 }
        } else { 0u8 };
        
        let sum = bit1 + bit2 + carry;
        result.push(if sum % 2 == 1 { '1' } else { '0' });
        carry = sum / 2;
        i = i + 1;
    }
    
    // Remove leading zeros
    while result.len() > 1 && result[result.len() - 1] == '0'
        invariant
            result.len() >= 1,
            ValidBitString(result@),
            Str2Int(result@) == Str2Int(s1@) + Str2Int(s2@)
        decreases result.len()
    {
        result.pop();
    }
    
    if result.len() == 0 {
        result.push('0');
    }
    
    result
}

// Helper to shift left (multiply by 2^n)
exec fn ShiftLeft(s: &[char], n: usize) -> (res: Vec<char>)
    requires ValidBitString(s@)
    ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s@) * pow2(n as nat)
{
    if s.len() == 1 && s[0] == '0' {
        let mut result = Vec::new();
        result.push('0');
        return result;
    }
    
    let mut result = Vec::new();
    for i in 0..n
        invariant
            0 <= i <= n,
            ValidBitString(result@),
            result@.len() == i,
            forall |j: int| 0 <= j < i ==> result@[j] == '0'
    {
        result.push('0');
    }
    
    for i in 0..s.len()
        invariant
            0 <= i <= s.len(),
            ValidBitString(result@),
            result@.len() == n + i,
            forall |j: int| 0 <= j < n ==> result@[j] == '0',
            forall |j: int| n <= j < n + i ==> result@[j] == s@[j - n]
    {
        result.push(s[i]);
    }
    
    result
}

spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

spec fn min(a: int, b: int) -> int {
    if a < b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    // Handle special case where either operand is zero
    if (s1.len() == 1 && s1[0] == '0') || (s2.len() == 1 && s2[0] == '0') {
        let mut result = Vec::new();
        result.push('0');
        return result;
    }
    
    let mut result = Vec::new();
    result.push('0');
    
    // Multiply s1 by each bit of s2
    for i in 0..s2.len()
        invariant
            0 <= i <= s2.len(),
            ValidBitString(result@),
            Str2Int(result@) == Str2Int(s1@) * Str2Int(s2@.subrange(0, i as int))
    {
        if s2[i] == '1' {
            let shifted = ShiftLeft(s1, i);
            result = AddBinary(&result, &shifted);
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}