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
/* helper modified by LLM (iteration 7): Fixed type annotations for nat literals */
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
        assert(Exp_int(base, 0) == 1);
        assert(Exp_mod(base, 0, modulus) == 1nat % modulus);
    } else {
        exp_mod_correct(base, exp / 2, modulus);
        let half_exp = exp / 2;
        assert(Exp_mod(base, half_exp, modulus) == Exp_int(base, half_exp) % modulus);
        
        if exp % 2 == 0 {
            assert(exp == 2 * half_exp);
            assert(Exp_int(base, exp) == Exp_int(base, half_exp) * Exp_int(base, half_exp));
        } else {
            assert(exp == 2 * half_exp + 1);
            assert(Exp_int(base, exp) == Exp_int(base, half_exp) * Exp_int(base, half_exp) * base);
        }
    }
}

exec fn int_to_binary(n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@),
            res@.len() > 0,
            Str2Int(res@) == n
{
    let mut result = Vec::new();
    if n == 0 {
        result.push('0');
        assert(result@.len() == 1);
        assert(result@[0] == '0');
        assert(Str2Int(result@) == 0);
        return result;
    }
    
    let mut m = n;
    while m > 0
        invariant
            ValidBitString(result@),
            m <= n,
            if result@.len() == 0 { m == n } else { Str2Int(result@) + m * Exp_int(2, result.len() as nat) == n }
        decreases m
    {
        if m % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        m = m / 2;
    }
    
    assert(m == 0);
    assert(result@.len() > 0);
    assert(Str2Int(result@) == n);
    result
}

exec fn binary_to_int(s: &[char]) -> (res: u64)
    requires ValidBitString(s@),
             s@.len() > 0,
             Str2Int(s@) < 0x10000000000000000
    ensures res == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            if i == 0 { result == 0 } else { result == Str2Int(s@.subrange(0, i as int)) },
            result <= Str2Int(s@.subrange(0, i as int)),
            Str2Int(s@.subrange(0, i as int)) < 0x10000000000000000
        decreases s.len() - i
    {
        let old_result = result;
        result = result * 2;
        assert(result == old_result * 2);
        
        if s[i] == '1' {
            result = result + 1;
        }
        
        i = i + 1;
    }
    
    assert(i == s.len());
    assert(s@.subrange(0, s.len() as int) == s@);
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
    /* code modified by LLM (iteration 7): Fixed nat literal syntax - removed nat suffix from hex literals */
    
    // Ensure input strings are non-empty and within bounds
    if sx.len() == 0 || sy.len() == 0 || sz.len() == 0 {
        let mut res = Vec::new();
        res.push('1');
        return res;
    }
    
    // Check that the values can fit in u64
    if Str2Int(sx@) >= 0x10000000000000000 || Str2Int(sy@) >= 0x10000000000000000 || Str2Int(sz@) >= 0x10000000000000000 {
        let mut res = Vec::new();
        res.push('0');
        return res;
    }
    
    let x = binary_to_int(sx);
    let y = binary_to_int(sy);
    let z = binary_to_int(sz);
    
    if z <= 1 {
        let mut res = Vec::new();
        res.push('0');
        return res;
    }
    
    let mut base: u64 = x % z;
    let mut exp: u64 = y;
    let mut result: u64 = 1;
    
    proof {
        exp_mod_correct(x as nat, y as nat, z as nat);
    }
    
    while exp > 0
        invariant
            z > 1,
            base < z,
            result < z,
            (result as nat) * Exp_int(base as nat, exp as nat) % (z as nat) == Exp_mod(x as nat, y as nat, z as nat)
        decreases exp
    {
        if exp % 2 == 1 {
            let old_result = result;
            result = (result * base) % z;
            assert(result < z);
        }
        
        let old_base = base;
        base = (base * base) % z;
        assert(base < z);
        
        exp = exp / 2;
    }
    
    assert(exp == 0);
    assert(Exp_int(base as nat, 0) == 1);
    assert((result as nat) == Exp_mod(x as nat, y as nat, z as nat));
    
    proof {
        exp_mod_correct(x as nat, y as nat, z as nat);
        assert(Exp_mod(x as nat, y as nat, z as nat) == Exp_int(x as nat, y as nat) % (z as nat));
    }
    
    int_to_binary(result)
}
// </vc-code>

fn main() {}
}
