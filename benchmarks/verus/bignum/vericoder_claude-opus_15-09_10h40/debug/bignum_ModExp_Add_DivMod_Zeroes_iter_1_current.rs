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
proof fn exp_mod_properties()
    ensures
        forall|x: nat, z: nat| z > 1 ==> Exp_int(x, 0) % z == 1 % z,
        forall|x: nat, y: nat, z: nat| y > 0 && z > 1 ==> Exp_int(x, y) % z == ((x % z) * (Exp_int(x, (y - 1) as nat) % z)) % z,
{}

proof fn str2int_shift_property(s: Seq<char>)
    requires
        ValidBitString(s),
        s.len() > 0,
    ensures
        Str2Int(s.subrange(0, s.len() as int - 1)) == Str2Int(s) / 2,
{}

fn int_to_bitstring(n: nat) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == n,
{
    if n == 0 {
        vec!['0']
    } else {
        let mut result = Vec::new();
        let mut num = n;
        while num > 0
            invariant
                ValidBitString(result@),
                n == num * Exp_int(2, result.len() as nat) + Str2Int(result@),
        {
            if num % 2 == 1 {
                result.push('1');
            } else {
                result.push('0');
            }
            num = num / 2;
        }
        result
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x_val = str_to_int(sx);
    let y_val = str_to_int(sy);
    let z_val = str_to_int(sz);
    
    if sy.len() == 0 || (sy.len() == 1 && sy[0] == '0') {
        proof {
            exp_mod_properties();
        }
        return int_to_bitstring(1 % z_val);
    }
    
    let last_bit = sy[sy.len() - 1];
    let sy_shifted = &sy[..sy.len() - 1];
    
    let half_result = ModExp_Add_DivMod_Zeroes(sx, sy_shifted, sz);
    let half_val = str_to_int(&half_result);
    
    let result_val = if last_bit == '1' {
        ((half_val * half_val) % z_val * (x_val % z_val)) % z_val
    } else {
        (half_val * half_val) % z_val
    };
    
    proof {
        exp_mod_properties();
        str2int_shift_property(sy@);
    }
    
    int_to_bitstring(result_val)
}
// </vc-code>

fn main() {}
}
