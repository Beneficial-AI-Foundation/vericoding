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
/* code modified by LLM (iteration 4): Fixed type casting for `carry` to be `ghost` by making the whole expression a ghost expression */
{
  let mut s1_vec = s1.to_vec();
  let mut s2_vec = s2.to_vec();
  s1_vec.reverse();
  s2_vec.reverse();

  let mut result_vec: Vec<char> = Vec::new();
  let mut carry: nat = 0;
  let mut i: usize = 0;
  let max_len: usize = if s1_vec.len() > s2_vec.len() { s1_vec.len() } else { s2_vec.len() };

  while i < max_len || carry > 0
    invariant
      carry >= 0,
      ValidBitString(result_vec@),
      carry <= 1,
  {
    let digit1 = if i < s1_vec.len() && (s1_vec.index(i as usize) == '1') { 1 } else { 0 };
    let digit2 = if i < s2_vec.len() && (s2_vec.index(i as usize) == '1') { 1 } else { 0 };

    let sum = digit1 + digit2 + carry;
    let current_digit = sum % 2;
    carry = (sum / 2) as nat; // This expression is now correctly inferred as ghost because sum is ghost, and / and % operations on nat types are ghost.

    result_vec.push_key(if current_digit == 1 { '1' } else { '0' });
    i = i + 1;
  }
  result_vec.reverse();
  if result_vec.is_empty() {
    return vec!['0'];
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
/* code modified by LLM (iteration 4): Add `bitstring_to_vec_char` helper */
{
  let dividend_val = Str2Int(dividend@);
  let divisor_val = Str2Int(divisor@);

  if dividend_val < divisor_val {
    return (vec!['0'], dividend.to_vec());
  }

  let mut quotient_vec: Vec<char> = Vec::new();
  let mut current_rem_val: nat = dividend_val;
  let mut quotient_val: nat = 0;

  while current_rem_val >= divisor_val
    invariant
      current_rem_val >= 0,
      divisor_val > 0,
      dividend_val == quotient_val * divisor_val + current_rem_val,
      quotient_val >= 0,
  {
    let mut k: nat = 0;
    let mut temp_divisor_for_subtraction: nat = divisor_val;
    proof {
      assert(current_rem_val >= divisor_val);
    }
    while (temp_divisor_for_subtraction << 1) <= current_rem_val
      invariant
        k >= 0,
        temp_divisor_for_subtraction >= divisor_val,
        divisor_val > 0,
        temp_divisor_for_subtraction == divisor_val * Exp_int(2, k),
    {
      temp_divisor_for_subtraction = temp_divisor_for_subtraction << 1;
      k = k + 1;
    }
    current_rem_val = current_rem_val - temp_divisor_for_subtraction;
    quotient_val = quotient_val + (1 << k);
  }

  let q_str = bitstring_to_vec_char(quotient_val);
  let r_str = bitstring_to_vec_char(current_rem_val);

  (q_str, r_str)
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): add `bitstring_to_vec_char` helper and remove `result_val` variable */
{
  let s1_val = Str2Int(s1@);
  let s2_val = Str2Int(s2@);

  if s1_val == 0 || s2_val == 0 {
    return vec!['0'];
  }

  let prod_val = s1_val * s2_val;

  bitstring_to_vec_char(prod_val)
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
/* code modified by LLM (iteration 4): Changed type for current_exp_val and its assignment. Add `bitstring_to_vec_char` helper. Removed redundant variables */
{
  let sx_val = Str2Int(sx@);
  let sy_val = Str2Int(sy@);
  let sz_val = Str2Int(sz@);
  let result_val: nat;

  if sy_val == 0 {
    result_val = 1 % sz_val;
  } else {
    let mut current_exp_val: nat = sy_val;
    let mut base = sx_val % sz_val;
    let mut res_acc: nat = 1;

    while current_exp_val > 0
      invariant
        current_exp_val >= 0,
        base >= 0,
        res_acc >= 0,
        sz_val > 1,
        res_acc * Exp_int(base, current_exp_val) % sz_val == Exp_int(sx_val, sy_val) % sz_val,
    {
      if current_exp_val % 2 == 1 {
        res_acc = (res_acc * base) % sz_val;
      }
      base = (base * base) % sz_val;
      current_exp_val = current_exp_val / 2;
    }
    result_val = res_acc;
  }

  bitstring_to_vec_char(result_val)
}
// </vc-code>

fn main() {}
}
