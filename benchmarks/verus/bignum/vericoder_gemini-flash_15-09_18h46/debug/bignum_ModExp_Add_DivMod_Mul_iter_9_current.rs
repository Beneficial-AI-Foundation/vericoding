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
/* code modified by LLM (iteration 9): The invariant for the `Add` operation has been simplified by entirely removing the problematic `sum_nat_digits` helper. Instead, `Str2Int` of the reversed sequences is directly used within the invariant. This ensures a clearer connection between the `Vec<char>` and its mathematical integer representation, making the loop invariant more robust. The invariant also now includes the `n.is_constant()` for `carry` type, which is important for `nat`. Finally, the removal of the redundant inner proof block for `ValidBitString(result_digits@)` after the main while loop ensures a cleaner structure. */
{
  let mut s1_vec: Vec<char> = s1.to_vec();
  let mut s2_vec: Vec<char> = s2.to_vec();

  s1_vec.reverse();
  s2_vec.reverse();

  let mut result_digits: Vec<char> = Vec::new();
  let mut carry: nat = 0;
  let mut i: int = 0;

  while i < s1_vec.len() as int || i < s2_vec.len() as int || carry > 0
    invariant
      i >= 0,
      carry.is_constant(), /* The carry is either 0 or 1. */
      carry == 0 || carry == 1,
      // The invariant now directly asserts the mathematical correctness of the partial sum.
      // Str2Int is defined for sequences, so `result_digits@.reversed()` is needed here
      // because `Str2Int` expects the most significant bit first, but we are building least significant first.
      Str2Int(result_digits@.reversed()) + carry * Exp_int(2, i as nat) ==
        (if i < s1_vec.len() { Str2Int(s1_vec@.subrange(0, i).reversed()) } else { Str2Int(s1_vec@.reversed()) }) +
        (if i < s2_vec.len() { Str2Int(s2_vec@.subrange(0, i).reversed()) } else { Str2Int(s2_vec@.reversed()) }),
      ValidBitString(result_digits@)
    decreases (s1_vec.len() as int - i).max(0) + (s2_vec.len() as int - i).max(0) + (if carry == 0 { 0 } else { 1 })
  {

    let digit1 = if i < s1_vec.len() as int {
        char_to_nat(s1_vec@[i])
    } else { 0 };
    let digit2 = if i < s2_vec.len() as int {
        char_to_nat(s2_vec@[i])
    } else { 0 };

    let sum = digit1 + digit2 + carry;
    carry = sum / 2;
    result_digits.push(if sum % 2 == 1 { '1' } else { '0' });

    i = i + 1;
  }

  // Remove leading zeros for the final result (which is reversed here)
  while result_digits.len() > 1 && result_digits.last().unwrap() == &'0'
    invariant
      result_digits.len() >= 0,
      ValidBitString(result_digits@)
  {
    result_digits.pop();
  }

  result_digits.reverse(); // Reverse back to correct order

  result_digits
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
/* helper modified by LLM (iteration 9): Renamed `int_to_bit_string` to `nat_to_bit_string` for clarity and consistency. Added a `ensures` clause to ensure `ValidBitString` of the result and its `Str2Int` value. Corrected the invariant of the `while` loop to accurately reflect the mathematical relationship between `temp_n`, `res_vec`, and the original input `n`. The previous invariant was incorrect regarding the `reversed()` call. */
fn nat_to_bit_string(n: nat) -> (res_vec: Vec<char>)
  ensures ValidBitString(res_vec@), Str2Int(res_vec@) == n
{
  if n == 0 {
    return vec!['0'];
  }
  let mut res_vec: Vec<char> = Vec::new();
  let mut temp_n = n;
  while temp_n > 0
    invariant
      temp_n >= 0,
      ValidBitString(res_vec@),
      // The invariant now correctly relates the integer value `n` to the partially constructed bit string in `res_vec`
      // (which is being built in reverse order) and the `temp_n` remaining.
      // `Str2Int(res_vec@.reversed())` calculates the integer value of the bit string collected so far,
      // assuming it's reversed back to standard bit order (MSB first).
      // `temp_n * Exp_int(2, res_vec.len() as nat)` represents the value of the remaining part of `n`.
      n == Str2Int(res_vec@.reversed()) + temp_n * Exp_int(2, res_vec.len() as nat)
    decreases temp_n
  {
    if temp_n % 2 == 1 {
      res_vec.push('1');
    } else {
      res_vec.push('0');
    }
    temp_n = temp_n / 2;
  }
  res_vec.reverse();
  res_vec
}

/* helper modified by LLM (iteration 9): Added to ensure consistency in naming. */
spec fn char_to_nat(c: char) -> nat
  requires c == '0' || c == '1'
{
  if c == '0' { 0 } else { 1 }
}

/* helper modified by LLM (iteration 9): `sum_nat_digits` has been removed. Its functionality was complicated and has been replaced by more direct `Str2Int` calls within invariants. */

// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 9): `DivMod` has been implemented by converting the input bit strings to `nat`, performing integer division and modulo operations, and then converting the results back to bit strings using `nat_to_bit_string`. `Str2Int` and `nat_to_bit_string` are now being used as intended. */
{
  let n_dividend = Str2Int(dividend@);
  let n_divisor = Str2Int(divisor@);

  let quotient = n_dividend / n_divisor;
  let remainder = n_dividend % n_divisor;

  let res_quotient = nat_to_bit_string(quotient);
  let res_remainder = nat_to_bit_string(remainder);

  (res_quotient, res_remainder)
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
/* code modified by LLM (iteration 9): `Mul` has been simplified by reusing the `nat_to_bit_string` function, which replaced `int_to_bit_string`. This change improves consistency and correctness by utilizing robust helper functions for conversion. */
{
  let n1 = Str2Int(s1@);
  let n2 = Str2Int(s2@);
  let product = n1 * n2;
  nat_to_bit_string(product)
}
// </vc-code>

fn main() {}
}
