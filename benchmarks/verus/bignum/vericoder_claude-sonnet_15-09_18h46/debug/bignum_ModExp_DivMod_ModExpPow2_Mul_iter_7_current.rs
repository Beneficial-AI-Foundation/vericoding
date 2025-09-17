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
/* helper modified by LLM (iteration 7): fixed nat literal usage in nat_to_bitstring function */
spec fn pow_mod_properties(base: nat, exp: nat, modulus: nat) -> bool
{
    modulus > 1 ==> (base % modulus < modulus && (base * base) % modulus == (base % modulus * base % modulus) % modulus)
}

proof fn exp_mod_correctness(base: nat, exp: nat, modulus: nat)
    requires modulus > 1
    ensures Exp_int(base, exp) % modulus < modulus
    decreases exp
{
    if exp == 0 {
        assert(Exp_int(base, exp) == 1);
        assert((1 as nat) % modulus < modulus);
    } else {
        exp_mod_correctness(base, (exp - 1) as nat, modulus);
        assert(Exp_int(base, exp) == base * Exp_int(base, (exp - 1) as nat));
    }
}

proof fn str2int_bounds(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) < Exp_int(2, s.len())
    decreases s.len()
{
    if s.len() == 0 {
        assert(Str2Int(s) == 0);
        assert(Exp_int(2, 0) == 1);
    } else {
        str2int_bounds(s.subrange(0, s.len() as int - 1));
    }
}

exec fn nat_to_bitstring(n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@),
            Str2Int(res@) == n
{
    if n == 0nat {
        let mut result = Vec::new();
        result.push('0');
        return result;
    }
    
    let mut result = Vec::new();
    let mut temp = n;
    while temp > 0nat
        invariant temp >= 0nat
    {
        if temp % 2nat == 1nat {
            result.push('1');
        } else {
            result.push('0');
        }
        temp = temp / 2nat;
    }
    result.reverse();
    return result;
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 7): removed nat literals, using proper integer types */
    if sy.len() == 0 {
        let mut result = Vec::new();
        result.push('1');
        return result;
    }
    
    if sy.len() == 1 && sy[0] == '0' {
        let mut result = Vec::new();
        result.push('1');
        return result;
    }
    
    if sy.len() == 1 && sy[0] == '1' {
        let base_mod: nat = Str2Int(sx@) % Str2Int(sz@);
        return nat_to_bitstring(base_mod);
    }
    
    let half_exp_len = sy.len() / 2;
    let sy_half = &sy[0..half_exp_len];
    let sy_remaining = &sy[half_exp_len..];
    
    let half_result = ModExp_DivMod_ModExpPow2_Mul(sx, sy_half, sz);
    let squared_result = ModExp_DivMod_ModExpPow2_Mul(&half_result, &['1', '0'], sz);
    
    if sy_remaining.len() == 0 {
        return squared_result;
    } else {
        let remaining_result = ModExp_DivMod_ModExpPow2_Mul(sx, sy_remaining, sz);
        let final_base: nat = Str2Int(squared_result@) * Str2Int(remaining_result@) % Str2Int(sz@);
        return nat_to_bitstring(final_base);
    }
}
// </vc-code>

fn main() {}
}
