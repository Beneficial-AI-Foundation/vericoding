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
/* code modified by LLM (iteration 4): Removed unnecessary `as nat` casts and adjusted invariants */
{
  let s1_val: nat = Str2Int(s1@);
  let s2_val: nat = Str2Int(s2@);
  let sum_val: nat = s1_val + s2_val;

  let mut result: Vec<char> = Vec::new();
  let mut current_sum: nat = sum_val;

  if current_sum == 0 {
    result.push('0');
    proof {
      assert(Str2Int(result@) == 0);
      assert(ValidBitString(result@));
    }
    return result;
  }

  while current_sum > 0
    invariant
      ValidBitString(result@),
      sum_val == current_sum * Exp_int(2, result@.len() as nat) + Str2Int(result@),
    decreases current_sum
  {
    let digit: nat = current_sum % 2;
    if digit == 1 {
      result.insert(0, '1');
    } else {
      result.insert(0, '0');
    }
    current_sum = current_sum / 2;
  }

  proof {
    assert(ValidBitString(result@));
    assert(Str2Int(result@) == sum_val);
  }
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
/* code modified by LLM (iteration 4): Removed unnecessary `as nat` casts and adjusted invariants */
{
  let dividend_val: nat = Str2Int(dividend@);
  let divisor_val: nat = Str2Int(divisor@);

  let mut quotient_vec: Vec<char> = Vec::new();
  let mut remainder_vec: Vec<char> = Vec::new();

  let quotient: nat = dividend_val / divisor_val;
  let remainder: nat = dividend_val % divisor_val;

  // Convert quotient to bit string
  let mut temp_quotient: nat = quotient;
  if temp_quotient == 0 {
    quotient_vec.push('0');
  }
  while temp_quotient > 0
    invariant
      ValidBitString(quotient_vec@),
      quotient == temp_quotient * Exp_int(2, quotient_vec@.len() as nat) + Str2Int(quotient_vec@),
    decreases temp_quotient
  {
    let digit: nat = temp_quotient % 2;
    if digit == 1 {
      quotient_vec.insert(0, '1');
    } else {
      quotient_vec.insert(0, '0');
    }
    temp_quotient = temp_quotient / 2;
  }
  proof {
    assert(Str2Int(quotient_vec@) == quotient);
  }

  // Convert remainder to bit string
  let mut temp_remainder: nat = remainder;
  if temp_remainder == 0 {
    remainder_vec.push('0');
  }
  while temp_remainder > 0
    invariant
      ValidBitString(remainder_vec@),
      remainder == temp_remainder * Exp_int(2, remainder_vec@.len() as nat) + Str2Int(remainder_vec@),
    decreases temp_remainder
  {
    let digit: nat = temp_remainder % 2;
    if digit == 1 {
      remainder_vec.insert(0, '1');
    } else {
      remainder_vec.insert(0, '0');
    }
    temp_remainder = temp_remainder / 2;
  }
  proof {
    assert(Str2Int(remainder_vec@) == remainder);
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
/* code modified by LLM (iteration 4): Removed unnecessary `as nat` casts and adjusted invariants */
{
  let x_val: nat = Str2Int(sx@);
  let y_val: nat = Str2Int(sy@);
  let z_val: nat = Str2Int(sz@);

  // y is constrained to be 2^n or 0
  let mut res_val: nat;
  if y_val == 0 {
    res_val = 1;
  } else {
    // y_val == 2^n
    // We need to calculate (x_val^(2^n)) % z_val
    // This is equivalent to (((x_val^2) % z_val)^2 ... ) % z_val n times
    res_val = x_val % z_val;
    let mut i: int = 0;
    while i < n
      invariant
        0 <= i <= n,
        res_val == Exp_int(x_val, Exp_int(2, i as nat)) % z_val,
      decreases n - i
    {
      res_val = (res_val * res_val) % z_val;
      i = i + 1;
    }
  }

  let mut result_vec: Vec<char> = Vec::new();
  let mut current_res: nat = res_val;

  if current_res == 0 {
    result_vec.push('0');
    proof {
      assert(Str2Int(result_vec@) == 0);
      assert(ValidBitString(result_vec@));
    }
    return result_vec;
  }

  while current_res > 0
    invariant
      ValidBitString(result_vec@),
      res_val == current_res * Exp_int(2, result_vec@.len() as nat) + Str2Int(result_vec@),
    decreases current_res
  {
    let digit: nat = current_res % 2;
    if digit == 1 {
      result_vec.insert(0, '1');
    } else {
      result_vec.insert(0, '0');
    }
    current_res = current_res / 2;
  }
  proof {
    assert(ValidBitString(result_vec@));
    assert(Str2Int(result_vec@) == res_val as nat);
  }
  result_vec
}
// </vc-code>

fn main() {}
}


