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
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Corrected type mismatches (nat vs int) and fixed `map` argument for character conversion, replaced `pow` with `pow_nat` */
{
  let x = Str2Int(s1@);
  let y = Str2Int(s2@);
  let product = x * y;

  let mut temp_product: nat = product;
  let mut result_vec = Vec::<char>::new();

  if temp_product == 0 {
      result_vec.push('0');
      return result_vec;
  }

  while temp_product > 0
      invariant
          temp_product >= 0,
          Str2Int(result_vec@.map(|_idx, c: char| c).reverse()) * 2_nat.pow_nat(result_vec@.len() as nat) + temp_product == product,
      decreases temp_product
  {
      if (temp_product % 2) as nat == 1 {
          result_vec.push('1');
      } else {
          result_vec.push('0');
      }
      temp_product = (temp_product / 2) as nat;
  }
  result_vec.reverse();
  result_vec
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
/* code modified by LLM (iteration 2): Corrected type mismatches (nat vs int) and fixed `map` argument for character conversion, replaced `pow` with `pow_nat` */
{
  let x_nat = Str2Int(sx@);
  let y_nat = Str2Int(sy@);
  let z_nat = Str2Int(sz@);
  
  let mut res_nat: nat = 1;
  let mut base_nat: nat = x_nat % z_nat;
  let mut exp_nat: nat = y_nat;

  while exp_nat > 0
      invariant
          base_nat < z_nat,
          res_nat < z_nat,
          // `res_nat * (base_nat.pow_nat(exp_nat)) % z_nat == Exp_int(x_nat, y_nat) % z_nat`, // `pow_nat` is not spec function.
          exp_nat >= 0,
      decreases exp_nat
  {
      if (exp_nat % 2) as nat == 1 {
          res_nat = (res_nat * base_nat) % z_nat;
      }
      base_nat = (base_nat * base_nat) % z_nat;
      exp_nat = (exp_nat / 2) as nat;
  }

  let mut temp_res: nat = res_nat;
  let mut result_vec = Vec::<char>::new();

  if temp_res == 0 {
      result_vec.push('0');
      return result_vec;
  }

  while temp_res > 0
      invariant
          temp_res >= 0,
          Str2Int(result_vec@.map(|_idx, c: char| c).reverse()) * 2_nat.pow_nat(result_vec@.len() as nat) + temp_res == res_nat,
      decreases temp_res
  {
      if (temp_res % 2) as nat == 1 {
          result_vec.push('1');
      } else {
          result_vec.push('0');
      }
      temp_res = (temp_res / 2) as nat;
  }
  result_vec.reverse();
  result_vec
}
// </vc-code>

fn main() {}
}
