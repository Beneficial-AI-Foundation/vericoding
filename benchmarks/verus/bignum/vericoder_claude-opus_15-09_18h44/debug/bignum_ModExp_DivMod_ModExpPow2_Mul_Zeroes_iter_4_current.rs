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
spec fn Exp_mod(base: nat, exp: nat, modulus: nat) -> nat
    recommends modulus > 0
    decreases exp
{
    if exp == 0 {
        1nat % modulus
    } else {
        let half = Exp_mod(base, exp / 2, modulus);
        let square = (half * half) % modulus;
        if exp % 2 == 0 {
            square
        } else {
            (square * base) % modulus
        }
    }
}

proof fn exp_mod_correct(base: nat, exp: nat, modulus: nat)
    requires modulus > 0
    ensures Exp_mod(base, exp, modulus) == Exp_int(base, exp) % modulus
    decreases exp
{
    if exp == 0 {
    } else {
        exp_mod_correct(base, exp / 2, modulus);
        assert(Exp_int(base, exp) == if exp % 2 == 0 { Exp_int(base, exp / 2) * Exp_int(base, exp / 2) } else { Exp_int(base, exp / 2) * Exp_int(base, exp / 2) * base });
    }
}

exec fn int_to_binary(n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@),
            Str2Int(res@) == n
{
    let mut result = Vec::new();
    if n == 0 {
        result.push('0');
        return result;
    }
    let mut m = n;
    /* helper modified by LLM (iteration 4): Added decreases clause to int_to_binary loop */
    while m > 0
        invariant
            ValidBitString(result@),
            Str2Int(result@) + m * Exp_int(2, result.len() as nat) == n
        decreases m
    {
        if m % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        m = m / 2;
    }
    result
}

exec fn binary_to_int(s: &[char]) -> (res: u64)
    requires ValidBitString(s@),
             Str2Int(s@) < 0x10000000000000000
    ensures res == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    /* helper modified by LLM (iteration 4): Added decreases clause to binary_to_int loop */
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result == Str2Int(s@.subrange(0, i as int)),
            result < 0x10000000000000000
        decreases s.len() - i
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
exec fn ModExp_DivMod_ModExpPow2_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Implementation with proper decreases clauses */
    let x = binary_to_int(sx);
    let y = binary_to_int(sy);
    let z = binary_to_int(sz);
    
    let mut base = x % z;
    let mut exp = y;
    let mut result: u64 = 1;
    
    while exp > 0
        invariant
            (result as nat) * Exp_int(base as nat, exp as nat) % (z as nat) == Exp_int(x as nat, y as nat) % (z as nat),
            z > 1
        decreases exp
    {
        if exp % 2 == 1 {
            result = (result * base) % z;
        }
        base = (base * base) % z;
        exp = exp / 2;
    }
    
    proof {
        exp_mod_correct(x as nat, y as nat, z as nat);
    }
    
    int_to_binary(result)
}
// </vc-code>

fn main() {}
}
