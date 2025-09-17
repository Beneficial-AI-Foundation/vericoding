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
/* code modified by LLM (iteration 2): Changed `current_sum` to `nat` and `current_sum /= 2;` to `current_sum = (current_sum / 2) as nat;` to fix compilation error. */
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
      current_sum >= 0
    decreases current_sum
  {
    let bit = if current_sum % 2 == 1 { '1' } else { '0' };
    result_vec.insert(0, bit);
    current_sum = (current_sum / 2) as nat;
  }

  // Ensure the invariant is established for verification of Str2Int later.
  // This loop explicitly converts binary to integer, so ValidBitString is trivially true.
  proof {
    assert forall |i: int| 0 <= i && i < result_vec@.len() as int implies (result_vec@[i] == '0' || result_vec@[i] == '1') by {
      // Each inserted character is either '0' or '1'
    }
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
/* code modified by LLM (iteration 2): Changed `current_quo` and `current_rem` to `nat` and `/=` to `= / as nat` to fix compilation errors. */
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
        current_quo >= 0
      decreases current_quo
    {
      let bit = if current_quo % 2 == 1 { '1' } else { '0' };
      quote_vec.insert(0, bit);
      current_quo = (current_quo / 2) as nat;
    }
  }

  let mut rem_vec: Vec<char> = Vec::new();
  let mut current_rem: nat = remainder_int;

  if current_rem == 0 {
    rem_vec.push('0');
  } else {
    while current_rem > 0
      invariant
        current_rem >= 0
      decreases current_rem
    {
      let bit = if current_rem % 2 == 1 { '1' } else { '0' };
      rem_vec.insert(0, bit);
      current_rem = (current_rem / 2) as nat;
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
/* code modified by LLM (iteration 2): Changed `res_int` and `exp` to be explicitly `nat` and replaced `/=` with `= / as nat` to resolve compilation errors. */
{
  let x_int = Str2Int(sx@);
  let y_int = Str2Int(sy@);
  let z_int = Str2Int(sz@);

  let mut res_int: nat = 1;
  let mut base: nat = x_int;
  let mut exp: nat = y_int;

  while exp > 0
    invariant
      res_int as int >= 0,
      base as int >= 0,
      exp as int >= 0,
      res_int % z_int * Exp_int(base, exp) % z_int == Exp_int(x_int, y_int) % z_int
    decreases exp
  {
    if exp % 2 == 1 {
      res_int = (res_int * base) % z_int;
    }
    base = (base * base) % z_int;
    exp = (exp / 2) as nat;
  }

  let mut result_vec: Vec<char> = Vec::new();
  let mut current_res: nat = res_int;

  if current_res == 0 {
    result_vec.push('0');
    return result_vec;
  }

  while current_res > 0
    invariant
      current_res >= 0
    decreases current_res
  {
    let bit = if current_res % 2 == 1 { '1' } else { '0' };
    result_vec.insert(0, bit);
    current_res = (current_res / 2) as nat;
  }

  proof {
    assert(ValidBitString(result_vec@));
  }

  result_vec
}
// </vc-code>

fn main() {}
}


