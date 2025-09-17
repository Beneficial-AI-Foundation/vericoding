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
/* code modified by LLM (iteration 4): Cast all integer literals and arithmetic results to `nat` where needed. Used `sy.len() - 1` for iteration limit. Replaced track_get with direct indexing. */
{
  let s1_nat = Str2Int(s1@);
  let s2_nat = Str2Int(s2@);
  let product_nat = s1_nat * s2_nat;

  let mut product_vec_rev: Vec<char> = Vec::new();
  let mut temp_product: nat = product_nat;

  if temp_product == (0 as nat) {
      product_vec_rev.push('0');
  } else {
      while temp_product > (0 as nat)
          invariant
              product_vec_rev@.len() >= 0,
              ValidBitString(product_vec_rev@),
              temp_product >= (0 as nat),
      {
          let digit = temp_product % (2 as nat);
          if digit == (0 as nat) {
              product_vec_rev.push('0');
          } else {
              product_vec_rev.push('1');
          }
          temp_product = temp_product / (2 as nat);
      }
  }

  let mut res_vec: Vec<char> = Vec::new();
  let mut i: usize = product_vec_rev.len();
  while i > 0
      invariant
          i <= product_vec_rev.len(),
          res_vec@.len() == product_vec_rev.len() - i,
          ValidBitString(res_vec@),
  {
      i = i - 1;
      res_vec.push(product_vec_rev[i]);
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
/* code modified by LLM (iteration 4): Cast all integer literals and arithmetic results to `nat` where needed. Used `sy.len() - 1` for iteration limit. Replaced track_get with direct indexing. */
{
  let n_nat: nat = n as nat;

  if n == 0 {
      let mut res_vec: Vec<char> = Vec::new();
      if Str2Int(sx@) % Str2Int(sz@) == (0 as nat) {
          res_vec.push('0');
      } else {
          res_vec.push('1');
      }
      proof {
          assert(Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@) == (Str2Int(sx@) % Str2Int(sz@)) % Str2Int(sz@));
      }
      res_vec
  } else {
      let two_pow_n = Exp_int(2 as nat, n_nat);
      let two_pow_n_minus_1 = Exp_int(2 as nat, (n_nat - 1) as nat);

      let mut sy_prefix_vec: Vec<char> = Vec::new();
      let mut k: usize = 0;
      while k < sy.len() - 1
          invariant
              k <= sy.len() - 1,
              sy_prefix_vec@.len() == k,
              ValidBitString(sy_prefix_vec@.subrange(0, k as int)) == ValidBitString(sy@.subrange(0, k as int)),
      {
          sy_prefix_vec.push(sy[k]);
          k = k + 1;
      }

      let sy_prefix = sy_prefix_vec.as_slice();

      let part1_mod_exp = ModExpPow2(sx, sy_prefix, (n_nat - 1) as int, sz);
      let part1_val = Str2Int(part1_mod_exp@);

      let part1_val_squared = part1_val * part1_val;

      let mut res_val = part1_val_squared % Str2Int(sz@);

      if sy[n as usize] == '1' {
          res_val = (res_val * Str2Int(sx@)) % Str2Int(sz@);
      }

      let mut res_vec_rev: Vec<char> = Vec::new();
      let mut temp_res: nat = res_val;

      if temp_res == (0 as nat) {
          res_vec_rev.push('0');
      } else {
          while temp_res > (0 as nat)
              invariant
                  res_vec_rev@.len() >= 0,
                  ValidBitString(res_vec_rev@),
                  temp_res >= (0 as nat),
          {
              let digit = temp_res % (2 as nat);
              if digit == (0 as nat) {
                  res_vec_rev.push('0');
              } else {
                  res_vec_rev.push('1');
              }
              temp_res = temp_res / (2 as nat);
          }
      }
      let mut final_res_vec: Vec<char> = Vec::new();
      let mut i: usize = res_vec_rev.len();
      while i > 0
          invariant
              i <= res_vec_rev.len(),
              final_res_vec@.len() == res_vec_rev.len() - i,
              ValidBitString(final_res_vec@),
      {
          i = i - 1;
          final_res_vec.push(res_vec_rev[i]);
      }
      final_res_vec
  }
}
// </vc-code>

fn main() {}
}


