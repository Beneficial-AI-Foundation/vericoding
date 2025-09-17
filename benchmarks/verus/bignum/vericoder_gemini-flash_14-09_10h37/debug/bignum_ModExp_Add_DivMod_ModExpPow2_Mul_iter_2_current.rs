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
/* code modified by LLM (iteration 2): Initial implementation for addition. */
{
    let mut result = Vec::<char>::new();
    let mut carry = 0;
    let mut i = 0;
    let mut j = 0;
    while i < s1.len() || j < s2.len() || carry > 0
      invariant
        i <= s1.len(), j <= s2.len(),
        carry == 0 || carry == 1
    {
        let digit1 = if i < s1.len() { if s1[s1.len() - 1 - i] == '1' { 1 } else { 0 } } else { 0 };
        let digit2 = if j < s2.len() { if s2[s2.len() - 1 - j] == '1' { 1 } else { 0 } } else { 0 };
        let sum = digit1 + digit2 + carry;
        result.insert(0, if sum % 2 == 1 { '1' } else { '0' });
        carry = sum / 2;
        if i < s1.len() { i = i + 1; }
        if j < s2.len() { j = j + 1; }
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
/* helper modified by LLM (iteration 2): Implemented int_to_bit_string for compilation errors. */
fn int_to_bit_string(n: nat) -> Vec<char> {
  if n == 0 {
    return vec!['0'];
  }
  let mut s = Vec::<char>::new();
  let mut num = n;
  while num > 0 {
    s.insert(0, if num % 2 == 1 { '1' } else { '0' });
    num = num / 2;
  }
  s
}

/* code modified by LLM (iteration 2): Refactored division logic and used helper. */
{
    let dividend_val = Str2Int(dividend@);
    let divisor_val = Str2Int(divisor@);

    if dividend_val < divisor_val {
        return (int_to_bit_string(0), int_to_bit_string(dividend_val));
    }

    let mut quotient_vec: Vec<char> = int_to_bit_string(0);
    let mut remainder_vec: Vec<char> = int_to_bit_string(dividend_val);

    while Str2Int(remainder_vec@) >= divisor_val
        invariant
            ValidBitString(quotient_vec@),
            ValidBitString(remainder_vec@),
            Str2Int(dividend@) == Str2Int(quotient_vec@) * divisor_val + Str2Int(remainder_vec@),
            divisor_val > 0
    {
        let mut temp_divisor_val = divisor_val;
        let mut power_of_2_val: nat = 1;

        while Str2Int(remainder_vec@) >= temp_divisor_val * 2 && temp_divisor_val * 2 > 0
            invariant
                power_of_2_val > 0,
                temp_divisor_val == divisor_val * power_of_2_val
        {
            temp_divisor_val = temp_divisor_val * 2;
            power_of_2_val = power_of_2_val * 2;
        }

        let new_remainder_val = Str2Int(remainder_vec@) - temp_divisor_val;
        let new_quotient_val = Str2Int(quotient_vec@) + power_of_2_val;

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
/* code modified by LLM (iteration 2): Fixed nat/int conversion issue and used helper. */
{
  let sx_val = Str2Int(sx@);
  let sy_val = Str2Int(sy@);
  let sz_val = Str2Int(sz@);

  if sy_val == 0 {
    return int_to_bit_string(1 % sz_val);
  }

  let mut acc_res: nat = sx_val % sz_val;
  let mut i: nat = 1;
  while i < sy_val
    invariant
      acc_res == Exp_int(sx_val, i) % sz_val,
      i <= sy_val
  {
    acc_res = (acc_res * acc_res) % sz_val;
    i = i * 2;
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
/* code modified by LLM (iteration 2): Used int_to_bit_string helper. */
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
/* code modified by LLM (iteration 2): Used int_to_bit_string helper. */
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
      exponent <= sy_val
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
