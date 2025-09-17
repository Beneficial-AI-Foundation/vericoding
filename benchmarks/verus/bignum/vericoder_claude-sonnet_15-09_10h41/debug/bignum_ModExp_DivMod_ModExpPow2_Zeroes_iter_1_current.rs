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

// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    if sy.len() == 0 {
        let mut result = Vec::new();
        result.push('1');
        return result;
    }
    
    if Str2Int(sy@) == 0 {
        let mut result = Vec::new();
        result.push('1');
        return result;
    }
    
    if Str2Int(sy@) == 1 {
        let base_mod = mod_operation(sx, sz);
        return base_mod;
    }
    
    let half_exp = divide_by_2(sy);
    let half_result = ModExp_DivMod_ModExpPow2_Zeroes(sx, &half_exp, sz);
    let squared = multiply_mod(&half_result, &half_result, sz);
    
    if sy[sy.len() - 1] == '1' {
        let base_mod = mod_operation(sx, sz);
        multiply_mod(&squared, &base_mod, sz)
    } else {
        squared
    }
}
// </vc-code>

fn main() {}
}
