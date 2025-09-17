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
        let half = pow_mod(base, exp / 2, modulus);
        (half * half) % modulus
    } else {
        (base * pow_mod(base, (exp - 1) as nat, modulus)) % modulus
    }
}

proof fn pow_mod_equiv(base: nat, exp: nat, modulus: nat)
    requires modulus > 0
    ensures pow_mod(base, exp, modulus) == Exp_int(base, exp) % modulus
    decreases exp
{
    if exp == 0 {
        assert(Exp_int(base, 0) == 1);
        assert(pow_mod(base, 0, modulus) == 1nat % modulus);
    } else if exp % 2 == 0 {
        pow_mod_equiv(base, exp / 2, modulus);
        assert(Exp_int(base, exp) == Exp_int(base, exp / 2) * Exp_int(base, exp / 2));
    } else {
        pow_mod_equiv(base, (exp - 1) as nat, modulus);
        assert(Exp_int(base, exp) == base * Exp_int(base, (exp - 1) as nat));
    }
}

exec fn int_to_bit_string(mut n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@)
{
    if n == 0 {
        return vec!['0'];
    }
    
    let mut result = Vec::new();
    while n > 0
        invariant ValidBitString(result@)
    {
        if n % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        n = n / 2;
    }
    
    result.reverse();
    result
}

exec fn bit_string_to_int(s: &[char]) -> (res: u64)
    requires ValidBitString(s@), s@.len() <= 64
    ensures res == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut i = 0;
    
    while i < s.len()
        invariant 0 <= i <= s.len(),
                  ValidBitString(s@),
                  result == Str2Int(s@.subrange(0, i as int))
    {
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        i += 1;
    }
    
    proof {
        assert(s@.subrange(0, s@.len() as int) =~= s@);
    }
    
    result
}

proof fn str2int_subrange_lemma(s: Seq<char>, i: int)
    requires ValidBitString(s), 0 <= i < s.len()
    ensures Str2Int(s.subrange(0, i + 1)) == 2 * Str2Int(s.subrange(0, i)) + (if s.index(i) == '1' { 1nat } else { 0nat })
{
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_int(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    if sy.len() == 0 {
        return vec!['1'];
    }
    
    if sy.len() == 1 && sy[0] == '0' {
        return vec!['1'];
    }
    
    if sx.len() <= 64 && sy.len() <= 64 && sz.len() <= 64 {
        let x = bit_string_to_int(sx);
        let y = bit_string_to_int(sy);
        let z = bit_string_to_int(sz);
        
        if z <= 1 {
            return vec!['0'];
        }
        
        let mut base = x % z;
        let mut exp = y;
        let mut result = 1u64;
        
        while exp > 0
            invariant z > 1,
                      result < z,
                      (result as nat * pow_mod(base as nat, exp as nat, z as nat)) % (z as nat) == Exp_int(x as nat, y as nat) % (z as nat)
        {
            if exp % 2 == 1 {
                result = (result * base) % z;
            }
            base = (base * base) % z;
            exp = exp / 2;
        }
        
        proof {
            pow_mod_equiv(Str2Int(sx@), Str2Int(sy@), Str2Int(sz@));
        }
        
        return int_to_bit_string(result);
    } else {
        let mid = sy.len() / 2;
        if mid == 0 {
            if sy[0] == '0' {
                return vec!['1'];
            } else {
                let x_val = bit_string_to_int(sx);
                let z_val = bit_string_to_int(sz);
                if z_val > x_val {
                    return int_to_bit_string(x_val);
                } else {
                    return int_to_bit_string(x_val % z_val);
                }
            }
        }
        
        let sy_half = &sy[0..mid];
        let temp_result = ModExp_int(sx, sy_half, sz);
        let squared = ModExp_int(&temp_result, sy_half, sz);
        
        if sy.len() % 2 == 1 {
            return ModExp_int(&squared, &sy[sy.len()-1..], sz);
        } else {
            return squared;
        }
    }
}
// </vc-code>

fn main() {}
}