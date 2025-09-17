
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
/* helper modified by LLM (iteration 5): changed to exec function and fixed comparison logic */
exec fn CompareBits(a: &[char], b: &[char]) -> (res: bool)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures res == (Str2Int(a@) >= Str2Int(b@))
{
  if a.len() > b.len() {
    true
  } else if a.len() < b.len() {
    false
  } else {
    for i in 0..a.len()
    {
      if a[i] != b[i] {
        return a[i] == '1';
      }
    }
    true
  }
}
// </vc-helpers>

// <vc-spec>
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): fixed while condition and invariant */
  let mut quotient = Vec::<char>::new();
  let mut remainder = Vec::new();
  
  for i in 0..dividend.len() {
    remainder.push(dividend[i]);
    
    while CompareBits(&remainder, divisor)
      invariant
        0 <= i,
        i < dividend.len(),
        ValidBitString(remainder@),
      decreases Str2Int(divisor@) - Str2Int(remainder@)
    {
      quotient.push('1');
      let mut temp = Vec::new();
      let mut carry = 0;
      let mut j = 0;
      
      while j < remainder.len() || carry > 0
        invariant
          ValidBitString(temp@),
          j <= remainder.len(),
          carry == 0 || carry == 1,
          Str2Int(temp@) + carry * (1 << (remainder.len() - j)) == 
            if j <= remainder.len() { Str2Int(remainder@.subrange(j as int, remainder.len() as int)) } else { 0 }
      {
        let rem_bit = if j < remainder.len() {
          if remainder[j] == '1' { 1 } else { 0 }
        } else {
          0
        };
        let div_bit = if j < divisor.len() {
          if divisor[j] == '1' { 1 } else { 0 }
        } else {
          0
        };
        let diff = rem_bit - div_bit - carry;
        
        if diff == 1 {
          temp.push('1');
          carry = 0;
        } else if diff == 0 {
          temp.push('0');
          carry = 0;
        } else if diff == -1 {
          temp.push('1');
          carry = 1;
        } else {
          temp.push('0');
          carry = 1;
        }
        
        j += 1;
      }
      
      remainder = temp;
      while remainder.len() > 0 && remainder[0] == '0' {
        remainder.remove(0);
      }
    }
    
    quotient.push('0');
  }
  
  while quotient.len() > 0 && quotient[0] == '0' {
    quotient.remove(0);
  }
  
  if quotient.len() == 0 {
    quotient.push('0');
  }
  
  if remainder.len() == 0 {
    remainder.push('0');
  }
  
  (quotient, remainder)
}
// </vc-code>

fn main() {}
}


