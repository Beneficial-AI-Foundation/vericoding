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
/* helper modified by LLM (iteration 2): Fixed type annotations for literals and type conversions */
spec fn mod_exp(base: nat, exp: nat, modulus: nat) -> nat
    recommends modulus > 1
    decreases exp
{
    if exp == 0 {
        1nat % modulus
    } else {
        let half = mod_exp(base, exp / 2, modulus);
        let half_squared = (half * half) % modulus;
        if exp % 2 == 0 {
            half_squared
        } else {
            (half_squared * base) % modulus
        }
    }
}

proof fn mod_exp_correct(base: nat, exp: nat, modulus: nat)
    requires modulus > 1
    ensures mod_exp(base, exp, modulus) == Exp_int(base, exp) % modulus
    decreases exp
{
    if exp == 0 {
        assert(Exp_int(base, 0) == 1);
        assert(mod_exp(base, 0, modulus) == 1nat % modulus);
    } else {
        let half_exp = exp / 2;
        mod_exp_correct(base, half_exp, modulus);
        assert(mod_exp(base, half_exp, modulus) == Exp_int(base, half_exp) % modulus);
        
        if exp % 2 == 0 {
            assert(exp == 2 * half_exp);
            assert(Exp_int(base, exp) == Exp_int(base, 2 * half_exp));
            assert(Exp_int(base, 2 * half_exp) == Exp_int(base, half_exp) * Exp_int(base, half_exp));
        } else {
            assert(exp == 2 * half_exp + 1);
            assert(Exp_int(base, exp) == base * Exp_int(base, (exp - 1) as nat));
            assert(Exp_int(base, (exp - 1) as nat) == Exp_int(base, 2 * half_exp));
            assert(Exp_int(base, 2 * half_exp) == Exp_int(base, half_exp) * Exp_int(base, half_exp));
        }
    }
}

exec fn int_to_binary(n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@),
            Str2Int(res@) == n
{
    let mut result = Vec::new();
    let mut remaining = n;
    if n == 0 {
        result.push('0');
    } else {
        while remaining > 0
            invariant
                ValidBitString(result@),
                Str2Int(result@) + remaining * Exp_int(2, result@.len() as nat) == n
        {
            if remaining % 2 == 1 {
                result.push('1');
            } else {
                result.push('0');
            }
            remaining = remaining / 2;
        }
    }
    result
}

exec fn binary_to_int(s: &[char]) -> (res: u64)
    requires ValidBitString(s@),
            Str2Int(s@) < u64::MAX
    ensures res == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result == Str2Int(s@.subrange(0, i as int)),
            result < u64::MAX
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
exec fn ModExp_DivMod(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed type conversions and modulo operations */
{
    let x_val = binary_to_int(sx);
    let y_val = binary_to_int(sy);
    let z_val = binary_to_int(sz);
    
    let mut base = x_val % z_val;
    let mut exp = y_val;
    let mut result: u64 = 1;
    
    while exp > 0
        invariant
            z_val > 1,
            z_val == Str2Int(sz@),
            (result as nat * Exp_int(base as nat, exp as nat)) % (z_val as nat) == Exp_int(x_val as nat, y_val as nat) % (z_val as nat),
            base < z_val,
            result < z_val
    {
        if exp % 2 == 1 {
            result = (result * base) % z_val;
        }
        base = (base * base) % z_val;
        exp = exp / 2;
    }
    
    proof {
        assert(exp == 0);
        assert(Exp_int(base as nat, 0) == 1);
        assert((result as nat) == Exp_int(x_val as nat, y_val as nat) % (z_val as nat));
        assert(x_val == Str2Int(sx@));
        assert(y_val == Str2Int(sy@));
        assert((result as nat) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    }
    
    let res = int_to_binary(result);
    proof {
        assert(Str2Int(res@) == result);
        assert((result as nat) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    }
    res
}
// </vc-code>

fn main() {}
}
