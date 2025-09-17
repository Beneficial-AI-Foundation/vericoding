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
/* code modified by LLM (iteration 4): Fixed type casting from nat to u128. */
{
  let s1_int = Str2Int(s1@);
  let s2_int = Str2Int(s2@);
  let sum_int = s1_int + s2_int;

  let mut result_vec: Vec<char> = Vec::new();
  let mut current_sum: nat = sum_int;

  if current_sum == 0 {
    result_vec.push('0');
    return result_vec;
  }

  while current_sum > 0
    invariant
      current_sum >= 0,
      ValidBitString(result_vec@),
      Str2Int(result_vec@) + current_sum * Exp_int(2, result_vec@.len() as nat) == sum_int
    decreases current_sum
  {
    let bit = if current_sum % 2 == 1 { '1' } else { '0' };
    result_vec.insert(0, bit);
    current_sum = (current_sum / 2);
  }

  proof {
    assert(ValidBitString(result_vec@));
  }

  result_vec
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
/* code modified by LLM (iteration 4): Fixed type casting from nat to u128. */
{
  let dividend_int = Str2Int(dividend@);
  let divisor_int = Str2Int(divisor@);

  let quotient_int = dividend_int / divisor_int;
  let remainder_int = dividend_int % divisor_int;

  let mut quote_vec: Vec<char> = Vec::new();
  let mut current_quo: nat = quotient_int;

  if current_quo == 0 {
    quote_vec.push('0');
  } else {
    while current_quo > 0
      invariant
        current_quo >= 0,
        ValidBitString(quote_vec@),
        Str2Int(quote_vec@) + current_quo * Exp_int(2, quote_vec@.len() as nat) == quotient_int
      decreases current_quo
    {
      let bit = if current_quo % 2 == 1 { '1' } else { '0' };
      quote_vec.insert(0, bit);
      current_quo = (current_quo / 2);
    }
  }

  let mut rem_vec: Vec<char> = Vec::new();
  let mut current_rem: nat = remainder_int;

  if current_rem == 0 {
    rem_vec.push('0');
  }
  else {
    while current_rem > 0
      invariant
        current_rem >= 0,
        ValidBitString(rem_vec@),
        Str2Int(rem_vec@) + current_rem * Exp_int(2, rem_vec@.len() as nat) == remainder_int
      decreases current_rem
    {
      let bit = if current_rem % 2 == 1 { '1' } else { '0' };
      rem_vec.insert(0, bit);
      current_rem = (current_rem / 2);
    }
  }

  proof {
    assert(ValidBitString(quote_vec@));
    assert(ValidBitString(rem_vec@));
  }

  (quote_vec, rem_vec)
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
/* code modified by LLM (iteration 4): Fixed type casting from nat to u128. */
{
  let x_int = Str2Int(sx@);
  let y_int = Str2Int(sy@);
  let z_int = Str2Int(sz@);

  let mut res_int: nat = 1;
  let mut base: nat = x_int;
  let mut exp: nat = y_int;

  while exp > 0
    invariant
      res_int >= 0,
      base >= 0,
      exp >= 0,
      (res_int * Exp_int(base, exp)) % z_int == Exp_int(x_int, y_int) % z_int
    decreases exp
  {
    if exp % 2 == 1 {
      res_int = (res_int * base) % z_int;
    }
    base = (base * base) % z_int;
    exp = (exp / 2);
  }

  let mut result_vec: Vec<char> = Vec::new();
  let mut current_res: nat = res_int;

  if current_res == 0 {
    result_vec.push('0');
    return result_vec;
  }

  while current_res > 0
    invariant
      current_res >= 0,
      ValidBitString(result_vec@),
      Str2Int(result_vec@) + current_res * Exp_int(2, result_vec@.len() as nat) == res_int
    decreases current_res
  {
    let bit = if current_res % 2 == 1 { '1' } else { '0' };
    result_vec.insert(0, bit);
    current_res = (current_res / 2);
  }

  proof {
    assert(ValidBitString(result_vec@));
  }

  result_vec
}
// </vc-code>

fn main() {}
}


