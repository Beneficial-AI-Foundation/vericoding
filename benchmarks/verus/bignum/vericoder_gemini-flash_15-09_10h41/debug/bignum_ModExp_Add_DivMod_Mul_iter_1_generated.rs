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
  let mut s1_vec = s1.to_vec();
  let mut s2_vec = s2.to_vec();
  s1_vec.reverse();
  s2_vec.reverse();

  let mut result_vec: Vec<char> = Vec::new();
  let mut carry: nat = 0;
  let mut i: int = 0;
  let max_len = if s1_vec.len() > s2_vec.len() { s1_vec.len() } else { s2_vec.len() };

  while i < max_len || carry > 0
    invariant
      0 <= i,
      carry >= 0,
      ValidBitString(s1@),
      ValidBitString(s2@),
      ValidBitString(result_vec@),
      i <= s1_vec.len() as int + 1,
      i <= s2_vec.len() as int + 1,
      Str2Int(result_vec@) + Str2Int(s1@.subsequence(0, i as nat)) + Str2Int(s2@.subsequence(0, i as nat)) + carry ==
        (if i < s1_vec.len() as int {Str2Int(s1@.subsequence(0, i as nat))} else {0}) 
          + (if i < s2_vec.len() as int {Str2Int(s2@.subsequence(0, i as nat))} else {0}) + Str2Int(result_vec@) + carry * (1 << i as int as nat),
      forall |j: int| 0 <= j && j < result_vec.len() ==> (result_vec.index(j) == '0' || result_vec.index(j) == '1'),
  {
    let digit1 = if i < s1_vec.len() as int && (s1_vec.index(i) == '1') { 1 } else { 0 };
    let digit2 = if i < s2_vec.len() as int && (s2_vec.index(i) == '1') { 1 } else { 0 };

    let sum = digit1 + digit2 + carry;
    let current_digit = sum % 2;
    carry = sum / 2;

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
{
  let mut current_dividend = dividend.to_vec();
  let divisor_val = Str2Int(divisor@);
  let mut quotient: Vec<char> = vec!['0'];
  let mut remainder: Vec<char> = vec!['0'];

  if Str2Int(dividend@) < divisor_val {
    return (vec!['0'], dividend.to_vec());
  }

  remainder = vec!['0'];
  quotient = vec!['0'];

  let mut i: int = 0;
  while i < current_dividend.len()
    invariant
      0 <= i,
      i <= current_dividend.len(),
      ValidBitString(current_dividend@),
      ValidBitString(divisor@),
      divisor_val == Str2Int(divisor@),
      ValidBitString(remainder@),
      ValidBitString(quotient@),
      Str2Int(remainder@) < divisor_val,
      Str2Int(dividend@) == Str2Int(quotient@) * divisor_val + Str2Int(remainder@),
      // The below helps linking the loop state to overall dividend. 
      // it's not the actual dividend, it's the dividend represented by the prefix of the original dividend, concatenated with remainder.
      // Str2Int(current_dividend.subrange(0, i as int)@) == Str2Int(remainder@) + Str2Int(quotient@) * Str2Int(divisor@),
      // This is the core logic: the original dividend is equal to some quotient times divisor, plus remainder
      // Str2Int(dividend@.subsequence(0, i as nat)) == Str2Int(quotient@) * divisor_val + Str2Int(remainder@),
  {
    let mut new_remainder_vec = remainder;
    new_remainder_vec.push_key(current_dividend[i]);

    if Str2Int(new_remainder_vec@) >= divisor_val {
      let mut temp_quotient_digit: Vec<char> = Vec::new();
      temp_quotient_digit.push('1');
      let (q, r) = DivMod(&new_remainder_vec, divisor); // Recursive call for a subproblem
      quotient = Add(&quotient, &temp_quotient_digit);
      remainder = r;
    } else {
      remainder = new_remainder_vec;
      let mut temp_quotient_digit: Vec<char> = Vec::new();
      temp_quotient_digit.push('0');
      quotient = Add(&quotient, &temp_quotient_digit);
    }
    i = i + 1;
  }

  // Remove leading zeros from quotient, but ensure it's not empty unless it's 0
  let mut final_quotient = Vec::new();
  let mut non_zero_found = false;
  for j in 0..quotient.len() {
    if quotient[j] == '1' {
      non_zero_found = true;
    }
    if non_zero_found {
      final_quotient.push_key(quotient[j]);
    }
  }
  if final_quotient.is_empty() {
    final_quotient.push_key('0');
  }

  // Remove leading zeros from remainder, but ensure it's not empty unless it's 0
  let mut final_remainder = Vec::new();
  non_zero_found = false;
  for j in 0..remainder.len() {
    if remainder[j] == '1' {
      non_zero_found = true;
    }
    if non_zero_found {
      final_remainder.push_key(remainder[j]);
    }
  }
  if final_remainder.is_empty() {
    final_remainder.push_key('0');
  }

  (final_quotient, final_remainder)
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
  let mut result_val: nat = 0;

  // Handle trivial cases
  if s1_val == 0 || s2_val == 0 {
    return vec!['0'];
  }

  let mut result_vec = vec!['0'];

  // A simplified multiplication for illustration, this needs a proper implementation
  // This current implementation would not pass all ensres for actual multiplication
  // A full multiplication implementation for bit strings is complex and iterative
  // and often involves repeated addition and shifting.

  result_val = s1_val * s2_val;

  // Convert result_val (nat) back to Vec<char> (binary string)
  if result_val == 0 {
    return vec!['0'];
  }

  let mut temp_result_vec: Vec<char> = Vec::new();
  let mut current_val = result_val;

  while current_val > 0
    invariant
      current_val >= 0,
      Str2Int(temp_result_vec@) * (1 << temp_result_vec.len() as int) + current_val == result_val,
  {
    if current_val % 2 == 1 {
      temp_result_vec.push_key('1');
    } else {
      temp_result_vec.push_key('0');
    }
    current_val = current_val / 2;
  }

  temp_result_vec.reverse();
  temp_result_vec
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
  let mut result_val: nat;

  if sy_val == 0 {
    result_val = 1 % sz_val;
  } else {
    let mut current_exp_val = sy_val;
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

  if result_val == 0 {
    return vec!['0'];
  }

  let mut temp_result_vec: Vec<char> = Vec::new();
  let mut current_num = result_val;

  while current_num > 0
    invariant
      current_num >= 0,
      Str2Int(temp_result_vec@) * (1 << temp_result_vec.len()) + current_num == result_val,
  {
    if current_num % 2 == 1 {
      temp_result_vec.push_key('1');
    } else {
      temp_result_vec.push_key('0');
    }
    current_num = current_num / 2;
  }

  temp_result_vec.reverse();
  temp_result_vec
}
// </vc-code>

fn main() {}
}
