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
{
  let s1_nat = Str2Int(s1@);
  let s2_nat = Str2Int(s2@);
  let product_nat = s1_nat * s2_nat;

  let mut product_vec_rev: Vec<char> = Vec::new();
  let mut temp_product = product_nat;

  if temp_product == 0 {
      product_vec_rev.push('0');
  } else {
      while temp_product > 0
          invariant
              product_vec_rev@.len() >= 0,
              ValidBitString(product_vec_rev@),
              temp_product >= 0,
      {
          let digit = temp_product % 2;
          if digit == 0 {
              product_vec_rev.push('0');
          } else {
              product_vec_rev.push('1');
          }
          temp_product = temp_product / 2;
      }
  }

  let mut res_vec: Vec<char> = Vec::new();
  let mut i = product_vec_rev.len() as int - 1;
  while i >= 0
      invariant
          i >= -1,
          i < product_vec_rev.len() as int,
          res_vec@.len() <= product_vec_rev.len() as int,
          ValidBitString(res_vec@),
  {
      res_vec.push(product_vec_rev.track_get(i as nat).get());
      i = i - 1;
  }

  proof {
      assert(Str2Int(res_vec@) == product_nat) by (nonlinear_arith);
  }

  res_vec
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
{
  if n == 0 {
      let mut res_vec: Vec<char> = Vec::new();
      if Str2Int(sx@) % Str2Int(sz@) == 0 {
          res_vec.push('0');
      } else {
          res_vec.push('1');
      }
      proof {
          assert(Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@) == (Str2Int(sx@) % Str2Int(sz@)) % Str2Int(sz@));
      }
      res_vec
  } else {
      let two_pow_n = Exp_int(2, n as nat);
      let two_pow_n_minus_1 = Exp_int(2, (n - 1) as nat);

      let mut sy_prefix_vec: Vec<char> = Vec::new();
      for i in 0..sy.len() - 1 {
          sy_prefix_vec.push(sy[i]);
      }

      let sy_prefix = sy_prefix_vec.as_slice();

      let part1_mod_exp = ModExpPow2(sx, sy_prefix, n - 1, sz);
      let part1_val = Str2Int(part1_mod_exp@);

      let part1_val_squared = part1_val * part1_val; // This will become big

      let mut res_val = part1_val_squared % Str2Int(sz@);

      if sy[n as nat] == '1' {
          res_val = (res_val * Str2Int(sx@)) % Str2Int(sz@);
      }

      let mut res_vec_rev: Vec<char> = Vec::new();
      let mut temp_res = res_val;

      if temp_res == 0 {
          res_vec_rev.push('0');
      } else {
          while temp_res > 0
              invariant
                  res_vec_rev@.len() >= 0,
                  ValidBitString(res_vec_rev@),
                  temp_res >= 0,
          {
              let digit = temp_res % 2;
              if digit == 0 {
                  res_vec_rev.push('0');
              } else {
                  res_vec_rev.push('1');
              }
              temp_res = temp_res / 2;
          }
      }
      let mut final_res_vec: Vec<char> = Vec::new();
      let mut i = res_vec_rev.len() as int - 1;
      while i >= 0
          invariant
              i >= -1,
              i < res_vec_rev.len() as int,
              final_res_vec@.len() <= res_vec_rev.len() as int,
              ValidBitString(final_res_vec@),
      {
          final_res_vec.push(res_vec_rev.track_get(i as nat).get());
          i = i - 1;
      }
      final_res_vec
  }
}
// </vc-code>

fn main() {}
}


