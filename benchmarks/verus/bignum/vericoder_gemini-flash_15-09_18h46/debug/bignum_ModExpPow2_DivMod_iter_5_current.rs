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
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected `_nat` suffixes. */
{
  let dividend_int: nat = Str2Int(dividend@);
  let divisor_int: nat = Str2Int(divisor@);

  let quotient_int: nat = dividend_int / divisor_int;
  let remainder_int: nat = dividend_int % divisor_int;

  let mut quotient_vec: Vec<char> = Vec::new();
  let mut remainder_vec: Vec<char> = Vec::new();

  // Convert quotient_int to bit string
  let mut q_temp: nat = quotient_int;
  if q_temp == 0 {
    quotient_vec.push('0');
  } else {
    while q_temp > 0
      invariant
        q_temp >= 0,
      decreases q_temp
    {
      if q_temp % 2 == 1 {
        quotient_vec.push('1');
      } else {
        quotient_vec.push('0');
      }
      q_temp = q_temp / 2;
    }
    quotient_vec.reverse();
  }

  // Convert remainder_int to bit string
  let mut r_temp: nat = remainder_int;
  if r_temp == 0 {
    remainder_vec.push('0');
  } else {
    while r_temp > 0
      invariant
        r_temp >= 0,
      decreases r_temp
    {
      if r_temp % 2 == 1 {
        remainder_vec.push('1');
      } else {
        remainder_vec.push('0');
      }
      r_temp = r_temp / 2;
    }
    remainder_vec.reverse();
  }

  (quotient_vec, remainder_vec)
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
/* code modified by LLM (iteration 5): Corrected `_nat` suffixes. */
{
  let x: nat = Str2Int(sx@);
  let y: nat = Str2Int(sy@);
  let z: nat = Str2Int(sz@);

  let mut product: nat = 1;
  let mut base: nat = x % z;
  let mut exponent: nat = y;

  while exponent > 0
    invariant
      z > 1,
      product * Exp_int(base, exponent) % z == Exp_int(x, y) % z,
      exponent >= 0,
      base < z,
    decreases exponent
  {
    if exponent % 2 == 1 {
      product = (product * base) % z;
    }
    base = (base * base) % z;
    exponent = exponent / 2;
  }

  let mut res_vec: Vec<char> = Vec::new();

  let mut temp_product: nat = product;
  if temp_product == 0 {
    res_vec.push('0');
  } else {
    while temp_product > 0
      invariant
        temp_product >= 0,
      decreases temp_product
    {
      if temp_product % 2 == 1 {
        res_vec.push('1');
      } else {
        res_vec.push('0');
      }
      temp_product = temp_product / 2;
    }
    res_vec.reverse();
  }

  res_vec
}
// </vc-code>

fn main() {}
}


