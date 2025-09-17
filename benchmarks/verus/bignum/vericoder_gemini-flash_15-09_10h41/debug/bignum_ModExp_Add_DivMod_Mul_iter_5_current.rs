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
/* code modified by LLM (iteration 5): Corrected `carry` type by making `sum` an `int`. */
{
  let mut s1_vec = s1.to_vec();
  let mut s2_vec = s2.to_vec();
  s1_vec.reverse();
  s2_vec.reverse();

  let mut result_vec: Vec<char> = Vec::new();
  let mut carry: int = 0;
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

    let sum = (digit1 + digit2 + carry) as int;
    let current_digit: int = sum % 2;
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
/* helper modified by LLM (iteration 5): Added `bitstring_to_vec_char` helper function. */
pure fn bitstring_to_vec_char(n: nat) -> Vec<char>
  ensures
    ValidBitString(result@),
    Str2Int(result@) == n,
  decreases n
{
  if n == 0 {
    return vec!['0'];
  }
  let mut result_vec: Vec<char> = Vec::new();
  let mut temp_n = n;
  while temp_n > 0
    invariant
      temp_n >= 0,
      ValidBitString(result_vec@),
      Str2Int(result_vec@) * Exp_int(2, temp_n.log_2() + 1) + temp_n == n, // This invariant is complex.
  {
    result_vec.push_key(if temp_n % 2 == 1 { '1' } else { '0' });
    temp_n = temp_n / 2;
  }
  result_vec.reverse();
  result_vec
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Used `bitstring_to_vec_char` for conversion. */
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
/* code modified by LLM (iteration 5): Used `bitstring_to_vec_char` for conversion. */
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
        Str2Int(bitstring_to_vec_char(res_acc)) * Exp_int(Str2Int(bitstring_to_vec_char(base)), current_exp_val) % sz_val == Exp_int(sx_val, sy_val) % sz_val,
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
