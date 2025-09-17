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
/* helper modified by LLM (iteration 6): Fixed spec function syntax and added proper returns */
spec fn nat_mod(a: nat, b: nat) -> nat {
    a % b
}

spec fn nat_div(a: nat, b: nat) -> nat {
    a / b
}

spec fn nat_mul(a: nat, b: nat) -> nat {
    a * b
}

proof fn exp_int_recursive(x: nat, y: nat)
    requires y > 0
    ensures Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat)
{
}

proof fn exp_int_zero_power(x: nat)
    ensures Exp_int(x, 0) == 1
{
}

proof fn mod_exp_property(x: nat, y: nat, z: nat)
    requires z > 1
    ensures Exp_int(x, y) % z == Exp_int(x % z, y) % z
{
    if y > 0 {
        mod_exp_property(x, (y - 1) as nat, z);
        exp_int_recursive(x, y);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 6): Added proper result variable declaration and handling */
{
    if sy.is_empty() {
        proof {
            exp_int_zero_power(Str2Int(sx@));
        }
        let mut result = Vec::new();
        result.push('1');
        return result;
    }
    
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    
    let mut x = x_val % z_val;
    let mut y = y_val;
    let mut result_val: nat = 1;
    
    while y > 0
        invariant
            result_val == Exp_int(x_val, y_val - y) % z_val,
            x == Exp_int(x_val % z_val, y_val - y + 1) % z_val,
            y >= 0,
        decreases y
    {
        if y % 2 == 1 {
            result_val = (result_val * x) % z_val;
        }
        x = (x * x) % z_val;
        y = y / 2;
    }
    
    let mut res_vec = Vec::new();
    let mut temp = result_val;
    
    while temp > 0
        invariant
            ValidBitString(res_vec@),
            Str2Int(res_vec@) == result_val % Exp_int(2, res_vec@.len() as nat),
            temp == result_val / Exp_int(2, res_vec@.len() as nat),
        decreases temp
    {
        if temp % 2 == 1 {
            res_vec.push('1');
        } else {
            res_vec.push('0');
        }
        temp = temp / 2;
    }
    
    if res_vec.is_empty() {
        res_vec.push('0');
    }
    
    res_vec.reverse();
    res_vec
}
// </vc-code>

fn main() {}
}
