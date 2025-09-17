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
  /* code modified by LLM (iteration 5): Fixed `nat` and `int` type usage within `exec` functions. */
  let i1: nat = Str2Int(s1@);
  let i2: nat = Str2Int(s2@);
  let result_int: nat = i1 * i2;
  let mut v: Vec<char> = Vec::new();
  let mut temp_val: nat = result_int;
  if temp_val == 0 {
    v.push('0');
  } else {
    while temp_val > 0 {
      if temp_val % 2 == 1 {
        v.push('1');
      } else {
        v.push('0');
      }
      temp_val = temp_val / 2;
    }
    v.reverse();
  }
  v
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
  /* code modified by LLM (iteration 5): Fixed `nat` and `int` type usage within `exec` functions, and `usize` for `Vec` operations. */
  if n == 0 {
    let one_vec: Vec<char> = vec!['1'];
    return one_vec;
  } else {
    let x_val: nat = Str2Int(sx@);
    let y_val: nat = Str2Int(sy@);
    let z_val: nat = Str2Int(sz@);

    if y_val == 0 {
      let mut v = Vec::new();
      v.push('1');
      return v;
    }

    let mut new_sy_vec: Vec<char> = Vec::new();
    let mut temp: nat = y_val / 2;
    if temp == 0 && (n - 1) >= 0 {
      // The new sy represents Exp_int(2, n-1), which is '0' if temp is 0.
      // And we need appropriate length for new_sy_vec to satisfy sy@.len() == (n as nat) + 1 (for next iteration)
      let limit: usize = (n as int - 1) as usize;
      if limit >= 0 {
        for _i in 0..=limit {
          new_sy_vec.push('0');
        }
      }
    } else {
      proof {
        assert(temp >= 0) by (nonlinear_arith);
      }

      let mut temp_divisor: nat = temp;
      if temp_divisor == 0 {
          new_sy_vec.push('0');
      } else {
          while temp_divisor > 0 {
              if temp_divisor % 2 == 1 {
                new_sy_vec.push('1');
              } else {
                new_sy_vec.push('0');
              }
              temp_divisor = temp_divisor / 2;
          }
          new_sy_vec.reverse();
      }

      // Pad with leading zeros if necessary to ensure correct length for sy@.len() == (n as nat) + 1 for next iteration
      let target_len: usize = (n as int - 1) as usize + 1;
      while new_sy_vec.len() < target_len {
          new_sy_vec.insert(0, '0');
      }
    }

    let recur_res_vec = ModExpPow2(sx, new_sy_vec.as_slice(), n - 1, sz);
    let recur_res_int: nat = Str2Int(recur_res_vec@);
    let final_res_int: nat;

    if (y_val % 2) == 1 {
      let s1: nat = (recur_res_int * recur_res_int) % z_val;
      final_res_int = (s1 * x_val) % z_val;
    } else {
      final_res_int = (recur_res_int * recur_res_int) % z_val;
    }

    let mut res_vec = Vec::new();
    let mut temp_val: nat = final_res_int;
    if temp_val == 0 {
      res_vec.push('0');
    } else {
      while temp_val > 0 {
        if (temp_val % 2) == 1 {
          res_vec.push('1');
        }
        else {
          res_vec.push('0');
        }
        temp_val = temp_val / 2;
      }
      res_vec.reverse();
    }
    res_vec
  }
}
// </vc-code>

fn main() {}
}


