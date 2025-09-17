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
/* helper modified by LLM (iteration 8): fix type mismatch by using nat literals and proper nat operations */
spec fn pow_mod_props(base: nat, exp: nat, modulus: nat) -> bool
{
    modulus > 1 ==> (base % modulus < modulus && (base * base) % modulus == (base % modulus * base % modulus) % modulus)
}

proof fn exp_mod_correctness(base: nat, exp: nat, modulus: nat)
    requires modulus > 1
    ensures Exp_int(base, exp) % modulus < modulus
{
}

spec fn nat_to_bit_string_valid(n: nat) -> bool
{
    true
}

fn nat_to_bit_string(n: nat) -> (result: Vec<char>)
    ensures ValidBitString(result@), Str2Int(result@) == n
{
    if n == 0nat {
        let mut res = Vec::new();
        res.push('0');
        res
    } else {
        let mut temp = n;
        let mut digits = Vec::new();
        while temp > 0nat
            invariant temp >= 0nat
        {
            if temp % 2nat == 0nat {
                digits.push('0');
            } else {
                digits.push('1');
            }
            temp = temp / 2nat;
        }
        digits.reverse();
        digits
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 8): fix type mismatches by using nat literals consistently */
    let base = Str2Int(sx@);
    let exp = Str2Int(sy@);
    let modulus = Str2Int(sz@);
    
    if exp == 0nat {
        return nat_to_bit_string(1nat % modulus);
    }
    
    let mut result = 1nat;
    let mut base_power = base % modulus;
    let mut remaining_exp = exp;
    
    while remaining_exp > 0nat
        invariant
            modulus > 1nat,
            result < modulus,
            base_power < modulus,
            result * Exp_int(base_power, remaining_exp) % modulus == Exp_int(base, exp) % modulus,
    {
        if remaining_exp % 2nat == 1nat {
            result = (result * base_power) % modulus;
        }
        base_power = (base_power * base_power) % modulus;
        remaining_exp = remaining_exp / 2nat;
    }
    
    nat_to_bit_string(result)
}
// </vc-code>

fn main() {}
}
