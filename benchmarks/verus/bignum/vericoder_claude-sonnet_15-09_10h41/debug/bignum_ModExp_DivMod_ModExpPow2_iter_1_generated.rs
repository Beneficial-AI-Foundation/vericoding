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
spec fn pow_mod_helper(base: nat, exp: nat, modulus: nat) -> nat
    requires modulus > 1
    decreases exp
{
    if exp == 0 {
        1 % modulus
    } else if exp % 2 == 0 {
        let half_exp = pow_mod_helper(base, exp / 2, modulus);
        (half_exp * half_exp) % modulus
    } else {
        (base * pow_mod_helper(base, exp - 1, modulus)) % modulus
    }
}

spec fn int_to_bitstring_helper(n: nat, acc: Seq<char>) -> Seq<char>
    decreases n
{
    if n == 0 {
        if acc.len() == 0 { seq!['0'] } else { acc }
    } else {
        let digit = if n % 2 == 1 { '1' } else { '0' };
        int_to_bitstring_helper(n / 2, seq![digit] + acc)
    }
}

exec fn bitstring_to_int(s: &[char]) -> (result: nat)
    requires ValidBitString(s@)
    ensures result == Str2Int(s@)
{
    let mut result: nat = 0;
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            ValidBitString(s@),
            result == Str2Int(s@.subrange(0, i as int))
    {
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        i = i + 1;
    }
    result
}

exec fn int_to_bitstring(n: nat) -> (result: Vec<char>)
    ensures ValidBitString(result@)
{
    if n == 0 {
        vec!['0']
    } else {
        let mut result = Vec::new();
        let mut temp = n;
        while temp > 0
            invariant temp >= 0
            decreases temp
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
exec fn ModExp_DivMod_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let base = bitstring_to_int(sx);
    let exp = bitstring_to_int(sy);
    let modulus = bitstring_to_int(sz);
    
    let mut result: nat = 1;
    let mut base_mod = base % modulus;
    let mut exp_remaining = exp;
    
    while exp_remaining > 0
        invariant
            exp_remaining >= 0,
            modulus > 1,
            result < modulus,
            (result * pow_mod_helper(base_mod, exp_remaining, modulus)) % modulus == Exp_int(base, exp) % modulus
        decreases exp_remaining
    {
        if exp_remaining % 2 == 1 {
            result = (result * base_mod) % modulus;
        }
        base_mod = (base_mod * base_mod) % modulus;
        exp_remaining = exp_remaining / 2;
    }
    
    int_to_bitstring(result)
}
// </vc-code>

fn main() {}
}
