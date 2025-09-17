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
    let mut carry = 0;
    let mut i = 0;
    let mut j = 0;
    while i < s1.len() || j < s2.len() || carry > 0
      invariant
        i <= s1.len(), j <= s2.len(),
        result.len() == i + j + (if carry > 0 { 1 } else { 0 }),
        carry == 0 || carry == 1,
        forall |k: int| 0 <= k && k < result.len() ==> (result@[k] == '0' || result@[k] == '1')
    {
        let digit1 = if i < s1.len() { if s1[s1.len() - 1 - i] == '1' { 1 } else { 0 } } else { 0 };
        let digit2 = if j < s2.len() { if s2[s2.len() - 1 - j] == '1' { 1 } else { 0 } } else { 0 };
        let sum = digit1 + digit2 + carry;
        result.insert(0, if sum % 2 == 1 { '1' } else { '0' });
        carry = sum / 2;
        if i < s1.len() { i = i + 1; } else if j < s2.len() { j = j + 1; }
    }
    if result.is_empty() { result.push('0'); }
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
    let zero_char_vec = vec!['0'];
    let zero_seq = zero_char_vec@;
    let one_char_vec = vec!['1'];
    let one_seq = one_char_vec@;

    let dividend_val = Str2Int(dividend@);
    let divisor_val = Str2Int(divisor@);

    if dividend_val < divisor_val {
        return (vec!['0'], dividend.to_vec());
    }

    let mut quotient_vec: Vec<char> = Vec::new();
    let mut remainder_vec: Vec<char> = dividend.to_vec();

    while Str2Int(remainder_vec@) >= divisor_val
        invariant
            ValidBitString(quotient_vec@),
            ValidBitString(remainder_vec@),
            Str2Int(dividend@) == Str2Int(quotient_vec@) * divisor_val + Str2Int(remainder_vec@) 
    {
        let mut temp_divisor_vec = divisor.to_vec();
        let mut power_of_2_vec = vec!['1'];

        while Str2Int(remainder_vec@) >= Str2Int(temp_divisor_vec@ * 2) && Str2Int(temp_divisor_vec@ * 2) > 0
            invariant
                ValidBitString(temp_divisor_vec@),
                ValidBitString(power_of_2_vec@),
                Str2Int(temp_divisor_vec@) == Str2Int(divisor@) * Str2Int(power_of_2_vec@)
        {
            temp_divisor_vec.push('0'); // Multiply by 2
            power_of_2_vec.push('0'); // Multiply by 2
        }

        let mut current_quotient_bit_vec = power_of_2_vec; // This is the power of 2 to add to quotient
        let mut sub_val = temp_divisor_vec;

        // Subtract sub_val from remainder_vec
        let mut new_remainder_val = Str2Int(remainder_vec@) - Str2Int(sub_val@);
        let mut new_quotient_val = Str2Int(quotient_vec@) + Str2Int(current_quotient_bit_vec@);

        remainder_vec = int_to_bit_string(new_remainder_val);
        quotient_vec = int_to_bit_string(new_quotient_val);
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
  let sx_val = Str2Int(sx@);
  let sy_val = Str2Int(sy@);
  let sz_val = Str2Int(sz@);

  if n == 0 {
    // sy == 1
    let res_val = sx_val % sz_val;
    return int_to_bit_string(res_val);
  }

  // sy is 2^n
  let mut current_x = sx_val;
  let mut current_sy_power = 1; // Represents 2^0
  let mut acc_res: nat = 1; // accumulator for the result

  while current_sy_power <= sy_val
    invariant
      current_sy_power == Exp_int(2, n - (sy@.len() - 1 - (current_x.count_ones() as nat)) ),
      acc_res == Exp_int(sx_val, current_sy_power / 2) % sz_val, // This invariant is tricky. Need to track the effective exponent.
      current_x % sz_val == current_x,
      current_sy_power <= sy_val + 1
  {
    // this needs to be a square and multiply approach
    // we know that sy_val is 2^n
    // so we can just square n times modulo sz_val
    if current_sy_power == 1 {
      acc_res = sx_val % sz_val;
    } else {
      acc_res = ( (acc_res as nat) * (acc_res as nat) ) % sz_val;
    }
    current_sy_power = current_sy_power * 2;
  }
  
  int_to_bit_string(acc_res)
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
  let s1_val = Str2Int(s1@);
  let s2_val = Str2Int(s2@);
  let product = s1_val * s2_val;

  int_to_bit_string(product)
}
// </vc-code>

// <vc-spec>
exec fn ModExp(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
  let sx_val = Str2Int(sx@);
  let sy_val = Str2Int(sy@);
  let sz_val = Str2Int(sz@);
  
  if sy_val == 0 {
    return int_to_bit_string(1 % sz_val);
  }

  let mut res_val: nat = 1;
  let mut base = sx_val % sz_val;
  let mut exponent = sy_val;

  while exponent > 0
    invariant
      res_val * Exp_int(base, exponent) % sz_val == Exp_int(sx_val, sy_val) % sz_val,
      base < sz_val,
      exponent < sy_val + 1
  {
    if exponent % 2 == 1 {
      res_val = (res_val * base) % sz_val;
    }
    base = (base * base) % sz_val;
    exponent = exponent / 2;
  }

  int_to_bit_string(res_val)
}
// </vc-code>

fn main() {}
}
