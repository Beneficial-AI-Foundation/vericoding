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
  if s.len() == 0 {
    0
  } else {
    2 * Str2Int(s.subrange(0, s.len() as int - 1))
      + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
  }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  // All characters must be '0' or '1'.
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
/* helper modified by LLM (iteration 4): Remove unused helper functions to address compilation error regarding `nat` and `int` types. */
// </vc-helpers>

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
/* code modified by LLM (iteration 4): Removed int/nat casts that were causing compilation errors. */
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);

    if y_int == 0 {
        let mut vec = Vec::<char>::new();
        vec.push('1');
        return vec;
    }

    let mut result_int: nat = 1;
    let mut base_mod_z: nat = x_int % z_int;
    let mut exponent_val: nat = y_int;

    while exponent_val > 0
        invariant
            result_int < z_int,
            base_mod_z < z_int,
            exponent_val <= y_int,
            x_int % z_int == (Str2Int(sx@)) % (Str2Int(sz@)),
            z_int == Str2Int(sz@)
        decreases exponent_val
    {
        if exponent_val % 2 == 1 {
            result_int = (result_int * base_mod_z) % z_int;
        }
        base_mod_z = (base_mod_z * base_mod_z) % z_int;
        exponent_val = exponent_val / 2;
    }

    let mut res_vec = Vec::<char>::new();
    let mut temp: nat = result_int;

    if temp == 0 {
        res_vec.push('0');
        return res_vec;
    }

    while temp > 0
        invariant result_int >= temp,
            forall |idx: int| 0 <= idx && idx < res_vec.len() ==> (res_vec@[idx] == '0' || res_vec@[idx] == '1')
        decreases temp
    {
        if temp % 2 == 1 {
            res_vec.insert(0, '1');
        } else {
            res_vec.insert(0, '0');
        }
        temp = temp / 2;
    }

    res_vec
}
// </vc-code>

fn main() {}
}


