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
/* helper modified by LLM (iteration 2): fixed nat literal usage for proper type inference */
exec fn bit_string_to_nat(s: &[char]) -> (result: nat)
    requires ValidBitString(s@)
    ensures result == Str2Int(s@)
{
    let mut result: nat = 0nat;
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            ValidBitString(s@),
            result == Str2Int(s@.subrange(0, i as int))
    {
        result = result * 2nat;
        if s[i] == '1' {
            result = result + 1nat;
        }
        i = i + 1;
    }
    result
}

exec fn nat_to_bit_string(n: nat) -> (result: Vec<char>)
    ensures ValidBitString(result@)
{
    if n == 0nat {
        let mut result = Vec::new();
        result.push('0');
        return result;
    }
    let mut result = Vec::new();
    let mut temp = n;
    while temp > 0nat
        invariant ValidBitString(result@)
    {
        if temp % 2nat == 0nat {
            result.push('0');
        } else {
            result.push('1');
        }
        temp = temp / 2nat;
    }
    let mut i = 0;
    let len = result.len();
    while i < len / 2
        invariant
            ValidBitString(result@),
            i <= len / 2
    {
        let temp_char = result[i];
        result.set(i, result[len - 1 - i]);
        result.set(len - 1 - i, temp_char);
        i = i + 1;
    }
    result
}

exec fn mod_exp(base: nat, exp: nat, modulus: nat) -> (result: nat)
    requires modulus > 1
    ensures result == Exp_int(base, exp) % modulus
{
    if exp == 0nat {
        return 1nat % modulus;
    }
    let mut result: nat = 1nat;
    let mut base_mod = base % modulus;
    let mut exp_remaining = exp;
    while exp_remaining > 0nat
        invariant
            modulus > 1,
            result < modulus,
            base_mod < modulus,
            (result * Exp_int(base_mod, exp_remaining)) % modulus == Exp_int(base, exp) % modulus
    {
        if exp_remaining % 2nat == 1nat {
            result = (result * base_mod) % modulus;
        }
        base_mod = (base_mod * base_mod) % modulus;
        exp_remaining = exp_remaining / 2nat;
    }
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed to use proper type-correct helper functions */
{
    let base = bit_string_to_nat(sx);
    let exp = bit_string_to_nat(sy);
    let modulus = bit_string_to_nat(sz);
    let result_nat = mod_exp(base, exp, modulus);
    let result_vec = nat_to_bit_string(result_nat);
    result_vec
}
// </vc-code>

fn main() {}
}
