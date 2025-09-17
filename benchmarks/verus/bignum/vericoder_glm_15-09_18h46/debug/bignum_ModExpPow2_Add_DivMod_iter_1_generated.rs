use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 { 0 } else { 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }) }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==> (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
  let mut result = Vec::<char>::new();
  let mut i = s1.len() as int;
  let mut j = s2.len() as int;
  let mut carry = false;
  
  while i > 0 || j > 0 || carry
      invariant
          0 <= i <= s1.len() as int,
          0 <= j <= s2.len() as int,
          ValidBitString(s1@.subrange(i, s1.len() as int)),
          ValidBitString(s2@.subrange(j, s2.len() as int)),
          ValidBitString(result@.rev()),
      decreases i + j
  {
      let digit1 = if i > 0 { s1[(i - 1) as usize] } else { '0' };
      let digit2 = if j > 0 { s2[(j - 1) as usize] } else { '0' };
      
      let (sum, new_carry) = match (digit1, digit2, carry) {
          ('1', '1', true) => ('1', true),
          ('1', '1', false) => ('0', true),
          ('1', '0', true) => ('0', true),
          ('1', '0', false) => ('1', false),
          ('0', '1', true) => ('0', true),
          ('0', '1', false) => ('1', false),
          ('0', '0', true) => ('1', false),
          ('0', '0', false) => ('0', false),
          (_, _, _) => panic!("Invalid binary digit"),
      };
      
      result.push(sum);
      carry = new_carry;
      
      if i > 0 { i -= 1; }
      if j > 0 { j -= 1; }
  }
  
  result.reverse();
  result
}
// </vc-code>

// <vc-spec>
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
  let dividend_int = Str2Int(dividend@) as int;
  let divisor_int = Str2Int(divisor@) as int;
  
  let quotient_int = dividend_int / divisor_int;
  let remainder_int = dividend_int % divisor_int;
  
  let mut quotient = Vec::<char>::new();
  let mut remainder = Vec::<char>::new();
  
  let mut q = quotient_int;
  if q == 0 {
      quotient.push('0');
  } else {
      while q > 0 {
          if q % 2 == 0 {
              quotient.insert(0, '0');
          } else {
              quotient.insert(0, '1');
          }
          q = q / 2;
      }
  }
  
  let mut r = remainder_int;
  if r == 0 {
      remainder.push('0');
  } else {
      while r > 0 {
          if r % 2 == 0 {
              remainder.insert(0, '0');
          } else {
              remainder.insert(0, '1');
          }
          r = r / 2;
      }
  }
  
  (quotient, remainder)
}
// </vc-code>

// <vc-spec>
exec fn ModExpPow2(sx: &[char], sy: &[char], n: int, sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    n >= 0,
    (Str2Int(sy@) == Exp_int(2, n as nat) || Str2Int(sy@) == 0),
    sy@.len() == (n as nat) + 1,
    Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases n
// </vc-spec>
// <vc-code>
{
  let x = Str2Int(sx@) as int;
  let y = Str2Int(sy@) as int;
  let z = Str2Int(sz@) as int;
  
  let mut result = 1 % z;
  let mut base = x % z;
  let mut exp = y;
  
  while exp > 0
      invariant
          result >= 0,
          base >= 0,
          exp >= 0,
          (result * Exp_int(base as nat, exp as nat)) % z == Exp_int(x as nat, y as nat) % z,
      decreases exp
  {
      if exp % 2 == 1 {
          result = (result * base) % z;
      }
      base = (base * base) % z;
      exp = exp / 2;
  }
  
  let mut binary_result = Vec::<char>::new();
  let mut r = result;
  
  if r == 0 {
      binary_result.push('0');
  } else {
      while r > 0 {
          if r % 2 == 0 {
              binary_result.insert(0, '0');
          } else {
              binary_result.insert(0, '1');
          }
          r = r / 2;
      }
  }
  
  binary_result
}
// </vc-code>

fn main() {}
}


