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
/* helper modified by LLM (iteration 10): use int type and casting for nat operations */
spec fn is_power_of_two(n: nat) -> bool {
    n > 0 && exists |k: nat| n == Exp_int(2, k)
}

spec fn bit_string_to_nat_helper(s: Seq<char>, acc: nat, pos: nat) -> nat
recommends ValidBitString(s)
decreases s.len()
{
    if s.len() == 0 { acc } else {
        let digit: nat = if s.index(0) == '1' { 1 } else { 0 };
        bit_string_to_nat_helper(s.subrange(1, s.len() as int), acc * 2 + digit, pos + 1)
    }
}

exec fn mod_exp_simple(base: nat, exp: nat, modulus: nat) -> (result: nat)
requires modulus > 1
ensures result == Exp_int(base, exp) % modulus
{
    let mut result: nat = 1nat;
    let mut base_mod: nat = base % modulus;
    let mut exp_remaining: nat = exp;
    
    while exp_remaining > 0nat
        invariant
            result < modulus,
            base_mod < modulus,
            Exp_int(base, exp) % modulus == (result * Exp_int(base_mod, exp_remaining)) % modulus
        decreases exp_remaining
    {
        if exp_remaining % 2nat == 1nat {
            result = (result * base_mod) % modulus;
        }
        base_mod = (base_mod * base_mod) % modulus;
        exp_remaining = exp_remaining / 2nat;
    }
    result
}

exec fn nat_to_bit_string(n: nat) -> (result: Vec<char>)
ensures ValidBitString(result@)
{
    if n == 0nat {
        let mut v = Vec::new();
        v.push('0');
        v
    } else {
        let mut result = Vec::new();
        let mut num: nat = n;
        while num > 0nat
            invariant ValidBitString(result@)
            decreases num
        {
            if num % 2nat == 1nat {
                result.push('1');
            } else {
                result.push('0');
            }
            num = num / 2nat;
        }
        result.reverse();
        result
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): use nat suffix for literals */
    let base = Str2Int(sx@);
    let exp = Str2Int(sy@);
    let modulus = Str2Int(sz@);
    
    let result_nat = mod_exp_simple(base, exp, modulus);
    let result_vec = nat_to_bit_string(result_nat);
    
    result_vec
}
// </vc-code>

fn main() {}
}
