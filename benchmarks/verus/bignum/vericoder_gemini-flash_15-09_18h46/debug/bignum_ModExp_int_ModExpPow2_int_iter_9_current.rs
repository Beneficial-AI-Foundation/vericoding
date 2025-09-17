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
/* helper modified by LLM (iteration 9): no changes */
spec fn ModExp_int(x: nat, y: nat, z: nat) -> nat
  requires z > 1
  decreases y
{
  if y == 0 {
    1
  } else if y % 2 == 0 {
    let res = ModExp_int(x, y / 2, z);
    (res * res) % z
  } else {
    let res = ModExp_int(x, (y - 1) as nat / 2, z);
    (x * res % z * res) % z
  }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_int_ModExpPow2_int(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 9): Removed explicit `as nat` casts which were causing compilation errors. Implicit type conversion is handled by Verus. */
{
  let x = Str2Int(sx@);
  let y = Str2Int(sy@);
  let z = Str2Int(sz@);

  let result_nat = ModExp_int(x, y, z);

  let mut result_vec = Vec::<char>::new();
  if result_nat == 0 {
      result_vec.push('0');
  } else {
      let mut temp_nat: nat = result_nat;
      while temp_nat > 0
          invariant
              temp_nat >= 0,
              forall |i: int| 0 <= i && i < result_vec.len() ==> (result_vec@.index(i) == '0' || result_vec@.index(i) == '1'),
          decreases temp_nat
      {
          if temp_nat % 2 == 1 {
              result_vec.insert(0, '1');
          } else {
              result_vec.insert(0, '0');
          }
          temp_nat = temp_nat / 2;
      }
  }

  result_vec
}
// </vc-code>

fn main() {}
}
