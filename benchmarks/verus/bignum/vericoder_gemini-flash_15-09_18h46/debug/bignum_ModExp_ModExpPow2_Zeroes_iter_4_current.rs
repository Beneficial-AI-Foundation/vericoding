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
/* helper modified by LLM (iteration 4): No changes */
spec fn ModExp_ModExpPow2(x: nat, y: nat, z: nat) -> nat
  decreases y
{
  if y == 0 {
    1
  } else if y == 1 {
    x % z
  } else {
    let rec_res = ModExp_ModExpPow2(x, y / 2, z);
    let sq_res = (rec_res * rec_res) % z;
    if y % 2 == 0 {
      sq_res
    } else {
      (sq_res * (x % z)) % z
    }
  }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Cast `temp_val` to `nat` instead of `int` to avoid compilation error, and adjust loop condition and assignments for `nat` type. */
{
  let x_int = Str2Int(sx@);
  let y_int = Str2Int(sy@);
  let z_int = Str2Int(sz@);
  let result_nat = ModExp_ModExpPow2(x_int, y_int, z_int);

  let mut res_vec = Vec::new();
  if result_nat == 0 {
      res_vec.push('0');
  } else {
      let mut temp_val: nat = result_nat;
      while temp_val > 0
          invariant
              temp_val >= 0,
              forall |i: int| 0 <= i && i < res_vec.len() ==> (res_vec[i] == '0' || res_vec[i] == '1')
          decreases temp_val
      {
          if temp_val % 2 == 1 {
              res_vec.push('1');
          } else {
              res_vec.push('0');
          }
          temp_val = (temp_val / 2) as nat;
      }
  }
  res_vec.reverse();
  res_vec
}
// </vc-code>

fn main() {}
}
