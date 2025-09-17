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
lemma lemma_str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{}

lemma lemma_str2int_single_zero()
    ensures Str2Int(seq!['0']) == 0
{}

lemma lemma_str2int_single_one()
    ensures Str2Int(seq!['1']) == 1
{}

lemma lemma_exp_base_case(x: nat)
    ensures Exp_int(x, 0) == 1
{}

lemma lemma_exp_one(x: nat)
    ensures Exp_int(x, 1) == x
{}

lemma lemma_mod_identity(a: nat, m: nat)
    requires m > 1
    ensures a % m < m
{}

spec fn char_to_nat(c: char) -> nat {
    if c == '1' { 1 } else { 0 }
}

lemma lemma_valid_bit_string_slice(s: Seq<char>, start: int, end: int)
    requires ValidBitString(s)
    requires 0 <= start <= end <= s.len()
    ensures ValidBitString(s.subrange(start, end))
{}

exec fn nat_to_bit_string(n: nat, modulus: nat) -> (result: Vec<char>)
    requires modulus > 1
    ensures ValidBitString(result@)
    ensures result@.len() > 0
    ensures Str2Int(result@) == n % modulus
{
    if n == 0 {
        vec!['0']
    } else {
        let mut result = Vec::new();
        let mut remaining = n % modulus;
        
        if remaining == 0 {
            result.push('0');
        } else {
            while remaining > 0
                invariant ValidBitString(result@)
                invariant remaining < modulus
            {
                if remaining % 2 == 1 {
                    result.push('1');
                } else {
                    result.push('0');
                }
                remaining = remaining / 2;
            }
            result.reverse();
        }
        result
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Add_Zeroes_DivMod_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    // Base cases
    if sy.len() == 0 {
        return vec!['1'];
    }
    
    if sy.len() == 1 && sy[0] == '0' {
        return vec!['1'];
    }
    
    if sy.len() == 1 && sy[0] == '1' {
        let x_val = Str2Int(sx@);
        let z_val = Str2Int(sz@);
        let result_val = x_val % z_val;
        return nat_to_bit_string(result_val, z_val);
    }
    
    // For simplicity, handle small cases directly
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    
    // Simple iterative modular exponentiation for small values
    let mut result = 1nat;
    let mut base = x_val % z_val;
    let mut exp = y_val;
    
    while exp > 0
        invariant result < z_val || result == 1
        invariant base < z_val
        invariant z_val > 1
    {
        if exp % 2 == 1 {
            result = (result * base) % z_val;
        }
        base = (base * base) % z_val;
        exp = exp / 2;
    }
    
    nat_to_bit_string(result, z_val)
}
// </vc-code>

fn main() {}
}