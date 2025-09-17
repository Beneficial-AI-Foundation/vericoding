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
    /* code modified by LLM (iteration 3): fixed type annotations and indexing */
    let mut result = Vec::<char>::new();
    
    if s.len() == 0 {
        result.push('0');
        return result;
    }
    
    let mut start_idx = 0;
    while start_idx < s.len() && s[start_idx] == '0'
        invariant
            start_idx <= s.len(),
            ValidBitString(s@),
    {
        start_idx += 1;
    }
    
    if start_idx == s.len() {
        result.push('0');
        return result;
    }
    
    let mut i = start_idx;
    while i < s.len()
        invariant
            start_idx <= i <= s.len(),
            ValidBitString(s@),
            ValidBitString(result@),
            start_idx < s.len() ==> s[start_idx as int] == '1',
    {
        result.push(s[i]);
        i += 1;
    }
    
    result
}
// </vc-code>

// <vc-helpers>
/* helper modified by LLM (iteration 3): removed requires/ensures from spec function */
spec fn AddHelper(s1: Seq<char>, s2: Seq<char>, carry: nat, pos1: int, pos2: int) -> (nat, Seq<char>)
    decreases pos1 + pos2
{
    if pos1 < 0 && pos2 < 0 {
        if carry == 0 {
            (0, seq![])
        } else {
            (0, seq!['1'])
        }
    } else {
        let bit1: nat = if pos1 >= 0 && pos1 < s1.len() { if s1[pos1] == '1' { 1 } else { 0 } } else { 0 };
        let bit2: nat = if pos2 >= 0 && pos2 < s2.len() { if s2[pos2] == '1' { 1 } else { 0 } } else { 0 };
        let sum = bit1 + bit2 + carry;
        let new_carry = sum / 2;
        let result_bit = if sum % 2 == 1 { '1' } else { '0' };
        let (_, rest) = AddHelper(s1, s2, new_carry, pos1 - 1, pos2 - 1);
        (0, rest.push(result_bit))
    }
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
    /* code modified by LLM (iteration 3): fixed type annotations */
    let mut result = Vec::<char>::new();
    let mut carry: usize = 0;
    let mut i1 = s1.len();
    let mut i2 = s2.len();
    
    while i1 > 0 || i2 > 0 || carry > 0
        invariant
            i1 <= s1.len(),
            i2 <= s2.len(),
            carry <= 1,
            ValidBitString(s1@),
            ValidBitString(s2@),
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
    
    result.reverse();
    result
}
// </vc-code>

fn main() {}
}


