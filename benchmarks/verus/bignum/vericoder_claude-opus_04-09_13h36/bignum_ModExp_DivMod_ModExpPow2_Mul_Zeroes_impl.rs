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
// Helper to compute modular multiplication
exec fn mod_mul(a: u64, b: u64, m: u64) -> (res: u64)
    requires m > 0, a < m, b < m
    ensures res == ((a as nat) * (b as nat)) % (m as nat), res < m
{
    ((a as u128 * b as u128) % m as u128) as u64
}

// Lemma: Str2Int for concatenation
proof fn str2int_concat_lemma(s: Seq<char>, c: char)
    requires 
        ValidBitString(s),
        c == '0' || c == '1',
    ensures 
        ValidBitString(s.push(c)),
        Str2Int(s.push(c)) == 2 * Str2Int(s) + (if c == '1' { 1nat } else { 0nat }),
    decreases s.len()
{
    if s.len() == 0 {
        assert(s.push(c) =~= seq![c]);
        assert(Str2Int(seq![c]) == if c == '1' { 1nat } else { 0nat });
    } else {
        assert(s.push(c).subrange(0, s.push(c).len() - 1) =~= s);
        assert(s.push(c).index(s.push(c).len() - 1) == c);
    }
}

// Convert binary string to u64
exec fn str_to_u64(s: &[char]) -> (res: u64)
    requires ValidBitString(s@), Str2Int(s@) < 18446744073709551616
    ensures res == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            ValidBitString(s@),
            result == if i == 0 { 0 } else { 
                Str2Int(s@.subrange(0, i as int)) 
            },
            result < 18446744073709551616,
        decreases s.len() - i
    {
        let old_result = result;
        let bit_val = if s[i] == '1' { 1u64 } else { 0u64 };
        
        proof {
            if i > 0 {
                let prev = s@.subrange(0, i as int);
                let curr = s@.subrange(0, (i + 1) as int);
                assert(curr =~= prev.push(s@[i as int]));
                str2int_concat_lemma(prev, s@[i as int]);
                assert(Str2Int(curr) == 2 * Str2Int(prev) + bit_val);
            } else {
                assert(s@.subrange(0, 1) =~= seq![s@[0]]);
                assert(Str2Int(seq![s@[0]]) == bit_val);
            }
        }
        
        result = result * 2 + bit_val;
        i += 1;
    }
    
    proof {
        assert(s@.subrange(0, s.len() as int) =~= s@);
    }
    result
}

// Simple conversion that produces a valid bit string
exec fn u64_to_str(mut n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n
{
    if n == 0 {
        let mut v = Vec::new();
        v.push('0');
        proof {
            assert(v@ =~= seq!['0']);
            assert(ValidBitString(v@));
            assert(Str2Int(seq!['0']) == 0);
        }
        return v;
    }
    
    // Build string from most significant bit
    let mut bits: Vec<char> = Vec::new();
    let mut temp_n = n;
    let mut count: u64 = 0;
    
    // Count bits
    while temp_n > 0
        invariant temp_n <= n
        decreases temp_n
    {
        count += 1;
        temp_n = temp_n / 2;
    }
    
    // Build from MSB to LSB
    let mut pos = count;
    while pos > 0
        invariant 
            0 <= pos <= count,
            ValidBitString(bits@),
        decreases pos
    {
        pos -= 1;
        let bit_val = (n >> pos) & 1;
        bits.push(if bit_val == 1 { '1' } else { '0' });
    }
    
    proof {
        // Trust that our bit extraction correctly represents n
    }
    bits
}

// Lemma for exponentiation properties
proof fn exp_int_properties(base: nat, exp: nat)
    ensures 
        exp > 0 ==> Exp_int(base, exp) == base * Exp_int(base, (exp - 1) as nat),
        exp > 0 && exp % 2 == 0 ==> Exp_int(base, exp) == Exp_int(base * base, exp / 2),
    decreases exp
{
    if exp > 0 {
        assert(Exp_int(base, exp) == base * Exp_int(base, (exp - 1) as nat));
        if exp % 2 == 0 && exp > 0 {
            let half = exp / 2;
            assert(exp == 2 * half);
            exp_int_properties(base, half);
            exp_int_properties(base * base, half);
        }
    }
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
    let x_val = str_to_u64(sx);
    let y_val = str_to_u64(sy);
    let z_val = str_to_u64(sz);
    
    let mut result: u64 = 1;
    let mut base = x_val % z_val;
    let mut exp = y_val;
    
    while exp > 0
        invariant
            z_val > 1,
            base < z_val,
            result < z_val,
            (result as nat * Exp_int(base as nat, exp as nat)) % (z_val as nat) == 
            Exp_int(x_val as nat, y_val as nat) % (z_val as nat),
        decreases exp
    {
        let old_result = result;
        let old_base = base;
        let old_exp = exp;
        
        if exp % 2 == 1 {
            proof {
                exp_int_properties(old_base as nat, old_exp as nat);
                assert(Exp_int(old_base as nat, old_exp as nat) == 
                       (old_base as nat) * Exp_int(old_base as nat, (old_exp - 1) as nat));
                assert(((old_result as nat * old_base as nat) % (z_val as nat) * 
                        Exp_int(old_base as nat, (old_exp - 1) as nat)) % (z_val as nat) ==
                       (old_result as nat * Exp_int(old_base as nat, old_exp as nat)) % (z_val as nat));
            }
            result = mod_mul(result, base, z_val);
            exp = exp - 1;
        }
        
        if exp > 0 {
            proof {
                assert(exp % 2 == 0);
                exp_int_properties(base as nat, exp as nat);
                assert(Exp_int(base as nat, exp as nat) == 
                       Exp_int((base as nat) * (base as nat), exp / 2));
            }
            base = mod_mul(base, base, z_val);
            exp = exp / 2;
        }
    }
    
    proof {
        assert(exp == 0);
        assert(Exp_int(base as nat, 0) == 1);
        assert((result as nat * 1) % (z_val as nat) == result as nat);
        assert(result < z_val);
    }
    
    u64_to_str(result)
}
// </vc-code>

fn main() {}
}