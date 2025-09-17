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
spec fn pow_mod(base: nat, exp: nat, modulus: nat) -> nat
    recommends modulus > 0
    decreases exp
{
    if exp == 0 {
        1nat % modulus
    } else if exp % 2 == 0 {
        let half_pow = pow_mod(base, exp / 2, modulus);
        (half_pow * half_pow) % modulus
    } else {
        (base * pow_mod(base, (exp - 1) as nat, modulus)) % modulus
    }
}

proof fn lemma_pow_mod_correct(base: nat, exp: nat, modulus: nat)
    requires modulus > 0
    ensures pow_mod(base, exp, modulus) == Exp_int(base, exp) % modulus
    decreases exp
{
    if exp == 0 {
    } else if exp % 2 == 0 {
        lemma_pow_mod_correct(base, exp / 2, modulus);
        assert(Exp_int(base, exp) == Exp_int(base, exp / 2) * Exp_int(base, exp / 2));
    } else {
        lemma_pow_mod_correct(base, (exp - 1) as nat, modulus);
        assert(Exp_int(base, exp) == base * Exp_int(base, (exp - 1) as nat));
    }
}

exec fn int_to_bitstring(mut n: u64) -> (result: Vec<char>)
    ensures ValidBitString(result@)
{
    let mut temp = Vec::new();
    if n == 0 {
        temp.push('0');
        return temp;
    }
    
    while n > 0
        invariant ValidBitString(temp@)
        decreases n
    {
        if n % 2 == 0 {
            temp.push('0');
        } else {
            temp.push('1');
        }
        n = n / 2;
    }
    
    // Manual reverse
    let mut result = Vec::new();
    let mut i = temp.len();
    while i > 0
        invariant ValidBitString(temp@), ValidBitString(result@)
        decreases i
    {
        i = i - 1;
        result.push(temp[i]);
    }
    
    result
}

exec fn bitstring_to_u64(s: &[char]) -> (result: u64)
    requires ValidBitString(s@), s@.len() <= 64
    ensures result as nat <= Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut i = 0;
    
    while i < s.len()
        invariant 
            0 <= i <= s.len(),
            ValidBitString(s@)
        decreases s.len() - i
    {
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        i += 1;
    }
    
    result
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
    if sy.len() == 0 {
        return int_to_bitstring(1);
    }
    
    let base_val = bitstring_to_u64(sx);
    let exp_val = bitstring_to_u64(sy);
    let mod_val = bitstring_to_u64(sz);
    
    if mod_val <= 1 {
        return int_to_bitstring(0);
    }
    
    let mut result: u64 = 1;
    let mut base: u64 = base_val % mod_val;
    let mut exp: u64 = exp_val;
    
    while exp > 0
        invariant mod_val > 1
        decreases exp
    {
        if exp % 2 == 1 {
            result = (result * base) % mod_val;
        }
        base = (base * base) % mod_val;
        exp = exp / 2;
    }
    
    int_to_bitstring(result)
}
// </vc-code>

fn main() {}
}