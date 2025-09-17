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
/* helper modified by LLM (iteration 8): add missing helper functions for bitstring conversion and modular exponentiation */
exec fn bitstring_to_int(s: &[char]) -> (result: u64)
    requires
        ValidBitString(s@),
        Str2Int(s@) < 0x10000000000000000,
    ensures
        result == Str2Int(s@),
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result == Str2Int(s@.subrange(0, i as int)),
            result < 0x10000000000000000,
    {
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        i = i + 1;
    }
    result
}

exec fn int_to_bitstring(n: u64) -> (result: Vec<char>)
    ensures
        ValidBitString(result@),
        Str2Int(result@) == n,
{
    if n == 0 {
        let mut result = Vec::<char>::new();
        result.push('0');
        return result;
    }
    
    let mut result = Vec::<char>::new();
    let mut temp = n;
    while temp > 0
        invariant
            temp <= n,
    {
        if temp % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        temp = temp / 2;
    }
    
    // Reverse the result
    let mut i: usize = 0;
    let mut j: usize = result.len() - 1;
    while i < j
        invariant
            0 <= i <= result.len(),
            0 <= j < result.len(),
            i + j == result.len() - 1,
    {
        let temp = result[i];
        result.set(i, result[j]);
        result.set(j, temp);
        i = i + 1;
        j = j - 1;
    }
    
    result
}

spec fn power_mod(x: nat, y: nat, m: nat) -> nat
    recommends m > 0
    decreases y
{
    if y == 0 {
        1 % m
    } else {
        (x * power_mod(x, (y - 1) as nat, m)) % m
    }
}

proof fn power_mod_correct(x: nat, y: nat, m: nat)
    requires m > 0
    ensures power_mod(x, y, m) == Exp_int(x, y) % m
    decreases y
{
    if y == 0 {
        assert(power_mod(x, 0, m) == 1 % m);
        assert(Exp_int(x, 0) == 1);
    } else {
        power_mod_correct(x, (y - 1) as nat, m);
        assert(power_mod(x, (y - 1) as nat, m) == Exp_int(x, (y - 1) as nat) % m);
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
        assert(power_mod(x, y, m) == (x * power_mod(x, (y - 1) as nat, m)) % m);
        assert(power_mod(x, y, m) == (x * (Exp_int(x, (y - 1) as nat) % m)) % m);
    }
}

exec fn mod_exp_exec(x: u64, y: u64, m: u64) -> (result: u64)
    requires
        m > 1,
        m < 0x100000000,
    ensures
        result == power_mod(x as nat, y as nat, m as nat),
{
    let mut result: u64 = 1;
    let mut base = x % m;
    let mut exp = y;
    
    while exp > 0
        invariant
            m > 1,
            m < 0x100000000,
            base < m,
            result < m,
    {
        if exp % 2 == 1 {
            result = ((result as u128 * base as u128) % (m as u128)) as u64;
        }
        base = ((base as u128 * base as u128) % (m as u128)) as u64;
        exp = exp / 2;
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 8): directly use helper functions without overflow checks */
{
    let x_val = bitstring_to_int(sx);
    let y_val = bitstring_to_int(sy);
    let z_val = bitstring_to_int(sz);
    
    proof {
        assert(x_val == Str2Int(sx@));
        assert(y_val == Str2Int(sy@));
        assert(z_val == Str2Int(sz@));
        assert(z_val > 1);
    }
    
    let result_val = mod_exp_exec(x_val, y_val, z_val);
    
    proof {
        power_mod_correct(x_val as nat, y_val as nat, z_val as nat);
        assert(result_val == power_mod(x_val as nat, y_val as nat, z_val as nat));
        assert(power_mod(x_val as nat, y_val as nat, z_val as nat) == Exp_int(x_val as nat, y_val as nat) % (z_val as nat));
        assert(result_val == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    }
    
    let result = int_to_bitstring(result_val);
    
    proof {
        assert(ValidBitString(result@));
        assert(Str2Int(result@) == result_val);
        assert(result_val == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    }
    
    result
}
// </vc-code>

fn main() {}
}
