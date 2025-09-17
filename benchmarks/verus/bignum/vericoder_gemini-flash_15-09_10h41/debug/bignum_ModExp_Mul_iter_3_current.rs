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
/* code modified by LLM (iteration 3): Changed `as nat` to `as nat` within `ghost` variable definitions to correctly apply `nat` type in ghost context */
{
  let x = Str2Int(s1@);
  let y = Str2Int(s2@);
  let product = x * y;

  let mut ghost temp_product_ghost: nat = product;
  let mut result_vec = Vec::<char>::new();

  if product == 0 {
      result_vec.push('0');
      return result_vec;
  }

  while temp_product_ghost > 0
      invariant
          temp_product_ghost >= 0,
          Str2Int(result_vec@.map(|_idx, c: char| c).reverse()) * Exp_int(2, result_vec@.len() as nat) + temp_product_ghost == product,
      decreases temp_product_ghost
  {
      if (temp_product_ghost % 2) == 1 {
          result_vec.push('1');
      } else {
          result_vec.push('0');
      }
      temp_product_ghost = (temp_product_ghost / 2) as nat;
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
/* code modified by LLM (iteration 3): Changed `as nat` to `as nat` within `ghost` variable definitions to correctly apply `nat` type in ghost context and fixed Exp_int in invariant */
{
  let x_nat = Str2Int(sx@);
  let y_nat = Str2Int(sy@);
  let z_nat = Str2Int(sz@);
  
  let mut res_nat: nat = 1;
  let mut base_nat: nat = x_nat % z_nat;
  let mut ghost exp_nat_ghost: nat = y_nat;

  while exp_nat_ghost > 0
      invariant
          base_nat < z_nat,
          res_nat < z_nat,
          res_nat * Exp_int(base_nat, exp_nat_ghost) % z_nat == Exp_int(x_nat, y_nat) % z_nat,
          exp_nat_ghost >= 0,
      decreases exp_nat_ghost
  {
      if (exp_nat_ghost % 2) == 1 {
          res_nat = (res_nat * base_nat) % z_nat;
      }
      base_nat = (base_nat * base_nat) % z_nat;
      exp_nat_ghost = (exp_nat_ghost / 2) as nat;
  }

  let mut ghost final_res_ghost: nat = res_nat;
  let mut result_vec = Vec::<char>::new();

  if final_res_ghost == 0 {
      result_vec.push('0');
      return result_vec;
  }

  while final_res_ghost > 0
      invariant
          final_res_ghost >= 0,
          Str2Int(result_vec@.map(|_idx, c: char| c).reverse()) * Exp_int(2, result_vec@.len() as nat) + final_res_ghost == res_nat,
      decreases final_res_ghost
  {
      if (final_res_ghost % 2) == 1 {
          result_vec.push('1');
      } else {
          result_vec.push('0');
      }
      final_res_ghost = (final_res_ghost / 2) as nat;
  }
  result_vec.reverse();
  result_vec
}
// </vc-code>

fn main() {}
}
