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
proof fn lemma_exp_zero(x: nat)
    ensures Exp_int(x, 0) == 1
{
}

proof fn lemma_exp_succ(x: nat, y: nat)
    ensures Exp_int(x, y + 1) == x * Exp_int(x, y)
{
}

proof fn lemma_exp_mod(x: nat, y: nat, z: nat)
    requires z > 0
    ensures Exp_int(x, y) % z == ((x % z) * (Exp_int(x, (y - 1) as nat) % z)) % z
{
}

exec fn int_to_binary(mut n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@),
            Str2Int(res@) == n
{
    let mut result = Vec::new();
    if n == 0 {
        result.push('0');
        return result;
    }
    
    while n > 0
        invariant
            ValidBitString(result@),
            n + Str2Int(result@) * Exp_int(2, result@.len() as nat) == old(n)
    {
        if n % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        n = n / 2;
    }
    result
}

exec fn modular_multiply(a: u64, b: u64, modulus: u64) -> (res: u64)
    requires modulus > 1,
            a < modulus,
            b < modulus
    ensures res == (a * b) % modulus,
            res < modulus
{
    ((a % modulus) * (b % modulus)) % modulus
}

exec fn modular_exp(base: u64, mut exp: u64, modulus: u64) -> (res: u64)
    requires modulus > 1
    ensures res == Exp_int(base, exp) % modulus
    decreases exp
{
    if exp == 0 {
        return 1 % modulus;
    }
    
    let mut result = 1u64;
    let mut base_mod = base % modulus;
    
    while exp > 0
        invariant
            modulus > 1,
            result < modulus,
            base_mod < modulus,
            (result * Exp_int(base_mod, exp)) % modulus == Exp_int(base, old(exp)) % modulus
        decreases exp
    {
        if exp % 2 == 1 {
            result = modular_multiply(result, base_mod, modulus);
        }
        if exp > 1 {
            base_mod = modular_multiply(base_mod, base_mod, modulus);
        }
        exp = exp / 2;
    }
    result
}

exec fn binary_to_int(s: &[char]) -> (res: u64)
    requires ValidBitString(s@),
            s@.len() <= 64
    ensures res == Str2Int(s@)
{
    let mut result = 0u64;
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
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
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    if sy.len() == 0 || sy[0] == '0' {
        let mut res = Vec::new();
        res.push('1');
        return res;
    }
    
    let x_int = binary_to_int(sx);
    let y_int = binary_to_int(sy);
    let z_int = binary_to_int(sz);
    
    let result_int = modular_exp(x_int, y_int, z_int);
    let result = int_to_binary(result_int);
    
    result
}
// </vc-code>

fn main() {}
}
