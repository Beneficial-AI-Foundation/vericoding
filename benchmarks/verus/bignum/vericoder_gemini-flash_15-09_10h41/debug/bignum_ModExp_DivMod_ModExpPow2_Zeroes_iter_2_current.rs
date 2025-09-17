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
/* helper modified by LLM (iteration 2): Changed helper to only provide the spec function */
spec fn ModExp_DivMod_ModExpPow2_Zeroes_helper(x: nat, y: nat, z: nat) -> nat
  decreases y
{
  if y == 0 {
    1
  } else if y == 1 {
    x % z
  } else {
    let partial_res = ModExp_DivMod_ModExpPow2_Zeroes_helper(x, (y / 2) as nat, z);
    let squared_res = (partial_res * partial_res) % z;
    if y % 2 == 0 {
      squared_res
    } else {
      (x * squared_res) % z
    }
  }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Updated `string_to_vec_char` with `seq_to_vec_char` as it was causing compilation error */
{
  let x_int = Str2Int(sx@);
  let y_int = Str2Int(sy@);
  let z_int = Str2Int(sz@);

  let result_int = ModExp_DivMod_ModExpPow2_Zeroes_helper(x_int, y_int, z_int);

  // Convert the result_int (nat) back to a binary string representation (Vec<char>)
  let mut res_vec = Vec::new();
  if result_int == 0 {
    res_vec.push('0');
  } else {
    let mut temp = result_int;
    while temp > 0
      invariant
        temp >= 0,
        res_vec.len() >= 0,
        forall |idx: int| 0 <= idx && idx < res_vec.len() ==> (res_vec@[idx] == '0' || res_vec@[idx] == '1'),
    {
      let bit = temp % 2;
      let digit = if bit == 1 { '1' } else { '0' };
      res_vec.insert(0, digit);
      temp = temp / 2;
    }
  }
  res_vec
}
// </vc-code>

fn main() {}
}
