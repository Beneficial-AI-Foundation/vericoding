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
{
  let dividend_int = Str2Int(dividend@);
  let divisor_int = Str2Int(divisor@);

  let quotient_int = dividend_int / divisor_int;
  let remainder_int = dividend_int % divisor_int;

  let mut quotient_vec: Vec<char> = Vec::new();
  let mut remainder_vec: Vec<char> = Vec::new();

  // Convert quotient_int to bit string
  let mut q_temp = quotient_int;
  while q_temp > 0
    invariant
      quotient_int == Str2Int(bit_vec_to_seq(quotient_vec@)) * 2_nat.pow(q_temp_log_pow2 as nat) + q_temp,
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
  if quotient_vec.is_empty() {
    quotient_vec.push('0');
  }
  quotient_vec.reverse();

  // Convert remainder_int to bit string
  let mut r_temp = remainder_int;
  while r_temp > 0
    invariant
      remainder_int == Str2Int(bit_vec_to_seq(remainder_vec@)) * 2_nat.pow(r_temp_log_pow2 as nat) + r_temp,
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
  if remainder_vec.is_empty() {
    remainder_vec.push('0');
  }
  remainder_vec.reverse();

  proof {
    assert(Str2Int(bit_vec_to_seq(quotient_vec@)) == quotient_int);
    assert(Str2Int(bit_vec_to_seq(remainder_vec@)) == remainder_int);
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
{
  let x = Str2Int(sx@);
  let y = Str2Int(sy@);
  let z = Str2Int(sz@);

  let mut product = 1_nat;
  let mut base = x % z;
  let mut exponent = y;

  let zero_char_vec = Vec::new();
  zero_char_vec.push('0');

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

  let mut temp_product = product;
  while temp_product > 0
    invariant
      product == Str2Int(bit_vec_to_seq(res_vec@)) * 2_nat.pow(temp_product_log_pow2 as nat) + temp_product,
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

  if res_vec.is_empty() {
    res_vec.push('0');
  }
  res_vec.reverse();

  proof {
    assert(Str2Int(bit_vec_to_seq(res_vec@)) == product);
  }

  res_vec
}
// </vc-code>

fn main() {}
}


