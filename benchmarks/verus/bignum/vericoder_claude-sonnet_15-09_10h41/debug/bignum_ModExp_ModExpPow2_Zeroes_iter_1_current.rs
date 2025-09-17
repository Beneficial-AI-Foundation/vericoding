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
spec fn pow_mod_properties(base: nat, exp: nat, modulus: nat) -> bool
{
    modulus > 1 ==> (base * base) % modulus == (base % modulus * base % modulus) % modulus
}

proof fn modular_arithmetic_lemma(a: nat, b: nat, m: nat)
    requires m > 1
    ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}

proof fn exp_reduction_lemma(base: nat, exp: nat, modulus: nat)
    requires modulus > 1, exp > 0
    ensures Exp_int(base, exp) % modulus == (base % modulus * Exp_int(base, exp - 1) % modulus) % modulus
{
}

fn char_to_digit(c: char) -> (result: nat)
    requires c == '0' || c == '1'
    ensures result == 0 || result == 1
{
    if c == '1' { 1 } else { 0 }
}

fn nat_to_bit_string(n: nat) -> (result: Vec<char>)
    ensures ValidBitString(result@)
{
    if n == 0 {
        let mut v = Vec::new();
        v.push('0');
        v
    } else {
        let mut result = Vec::new();
        let mut temp = n;
        while temp > 0
            invariant ValidBitString(result@)
        {
            if temp % 2 == 1 {
                result.push('1');
            } else {
                result.push('0');
            }
            temp = temp / 2;
        }
        result.reverse();
        result
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
{
    if sy.len() == 1 && sy[0] == '0' {
        let mut result = Vec::new();
        result.push('1');
        return result;
    }
    
    let base_val = Str2Int(sx@);
    let exp_val = Str2Int(sy@);
    let mod_val = Str2Int(sz@);
    
    if exp_val == 0 {
        let mut result = Vec::new();
        result.push('1');
        return result;
    }
    
    let mut result_val = 1nat;
    let mut base_mod = base_val % mod_val;
    let mut exp_remaining = exp_val;
    
    while exp_remaining > 0
        invariant
            exp_remaining <= exp_val,
            result_val < mod_val,
            base_mod < mod_val,
            Exp_int(base_mod, exp_remaining) * result_val % mod_val == Exp_int(base_val, exp_val) % mod_val
    {
        if exp_remaining % 2 == 1 {
            result_val = (result_val * base_mod) % mod_val;
        }
        base_mod = (base_mod * base_mod) % mod_val;
        exp_remaining = exp_remaining / 2;
    }
    
    nat_to_bit_string(result_val)
}
// </vc-code>

fn main() {}
}
