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

// <vc-helpers>
/* helper modified by LLM (iteration 7): Added helper for displaying bit string to avoid code duplication */
fn int_to_bit_string(n: nat) -> (res: Vec<char>)
  ensures ValidBitString(res@) && Str2Int(res@) == n
{
  let mut result_vec = Vec::<char>::new();
  if n == 0 {
    result_vec.push('0');
    return result_vec;
  }
  let mut temp_n = n;
  while temp_n > 0
    invariant
      temp_n >= 0,
      ValidBitString(result_vec@),
      Str2Int(result_vec@) + Str2Int(int_to_bit_string_preserves_trailing_zeros(temp_n)) == Str2Int(int_to_bit_string(n)), // This invariant is not directly checkable here, but illustrates the idea
    decreases temp_n
  {
    if (temp_n % 2) == 1 {
      result_vec.insert(0, '1');
    } else {
      result_vec.insert(0, '0');
    }
    temp_n = (temp_n / 2) as nat;
  }
  result_vec
}

proof fn int_to_bit_string_preserves_trailing_zeros(n: nat) -> nat
  ensures Str2Int(int_to_bit_string(n)) == n
{
  if n == 0 { assert(Str2Int(int_to_bit_string(0)@) == 0); return 0; }
  let mut temp_n = n;
  let mut result_vec = Vec::<char>::new();
  while temp_n > 0
    invariant
      temp_n >= 0,
      (Str2Int(result_vec@) as nat) + temp_n * Exp_int(2, result_vec.len() as nat) == n,
    decreases temp_n
  {
    if temp_n % 2 == 1 {
      result_vec.insert(0, '1');
    } else {
      result_vec.insert(0, '0');
    }
    temp_n = temp_n / 2;
  }
  Str2Int(result_vec@)
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 7): Refactored ghost let declarations to be non-ghost and fixed semicolons. Utilized int_to_bit_string helper. */
{
    if Str2Int(sy@) == 0 {
        let mut vec_res = Vec::<char>::new();
        vec_res.push('1');
        vec_res
    } else if Str2Int(sy@) == 1 {
        let mut res_vec = Vec::<char>::new();
        for i in 0..sx.len() {
            res_vec.push(sx[i]);
        }
        res_vec
    } else if (Str2Int(sy@) % 2) == 0 {
        // Even exponent
        let half_sy_int: nat = (Str2Int(sy@) / 2) as nat;
        let half_sy_vec = int_to_bit_string(half_sy_int);

        let result_half = ModExp_DivMod_Mul_Zeroes(sx, &half_sy_vec.view_as_slice(), sz);
        let result_int: nat = (Str2Int(result_half@) * Str2Int(result_half@)) % Str2Int(sz@);
        let result_vec = int_to_bit_string(result_int);
        result_vec
    } else {
        // Odd exponent
        let sy_minus_1_int: nat = (Str2Int(sy@) - 1) as nat;
        let sy_minus_1_vec = int_to_bit_string(sy_minus_1_int);

        let result_sy_minus_1 = ModExp_DivMod_Mul_Zeroes(sx, &sy_minus_1_vec.view_as_slice(), sz);
        let result_int: nat = (Str2Int(sx@) * Str2Int(result_sy_minus_1@)) % Str2Int(sz@);
        let result_vec = int_to_bit_string(result_int);
        result_vec
    }
}
// </vc-code>

fn main() {}
}
