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
// Helper function to convert an integer back to a binary string
spec fn Int2Str(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq!['0']
    } else if n == 1 {
        seq!['1']
    } else {
        Int2Str(n / 2).push(if n % 2 == 0 { '0' } else { '1' })
    }
}

// Proof that Int2Str produces valid bit strings
proof fn Int2Str_valid(n: nat)
    ensures ValidBitString(Int2Str(n))
    decreases n
{
    if n <= 1 {
    } else {
        Int2Str_valid(n / 2);
    }
}

// Proof that Str2Int(Int2Str(n)) == n for small values
proof fn Str2Int_Int2Str_inverse(n: nat)
    requires n < 1000000  // Reasonable bound for practical use
    ensures Str2Int(Int2Str(n)) == n
    decreases n
{
    if n == 0 {
        assert(Int2Str(0) == seq!['0']);
        assert(Str2Int(seq!['0']) == 0);
    } else if n == 1 {
        assert(Int2Str(1) == seq!['1']);
        assert(Str2Int(seq!['1']) == 1);
    } else {
        Str2Int_Int2Str_inverse(n / 2);
        let s = Int2Str(n / 2);
        let bit = if n % 2 == 0 { '0' } else { '1' };
        assert(Int2Str(n) == s.push(bit));
        assert(Str2Int(s.push(bit)) == 2 * Str2Int(s) + (if bit == '1' { 1 } else { 0 }));
    }
}

// Helper to compute modular multiplication
exec fn mod_mul(a: u64, b: u64, m: u64) -> (res: u64)
    requires m > 0, a < m, b < m
    ensures res == ((a as nat) * (b as nat)) % (m as nat)
{
    ((a as u128 * b as u128) % m as u128) as u64
}

// Convert binary string to u64
exec fn str_to_u64(s: &[char]) -> (res: u64)
    requires ValidBitString(s@), Str2Int(s@) < 18446744073709551616  // 2^64
    ensures res == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant {
            0 <= i <= s.len() &&
            result == Str2Int(s@.subrange(0, i as int)) &&
            Str2Int(s@.subrange(0, i as int)) < 18446744073709551616
        }
    {
        result = result * 2 + if s[i] == '1' { 1 } else { 0 };
        i += 1;
    }
    
    assert(s@.subrange(0, s.len() as int) == s@);
    result
}

// Convert u64 to binary string
exec fn u64_to_str(mut n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@)
    ensures Str2Int(res@) == n
{
    if n == 0 {
        let mut v = Vec::new();
        v.push('0');
        return v;
    }
    
    let mut result = Vec::new();
    let mut temp = Vec::new();
    
    while n > 0
        invariant {
            ValidBitString(temp@)
        }
    {
        temp.push(if n % 2 == 0 { '0' } else { '1' });
        n = n / 2;
    }
    
    // Reverse the temp vector
    let mut i: usize = temp.len();
    while i > 0
        invariant {
            0 <= i <= temp.len() &&
            ValidBitString(result@) &&
            ValidBitString(temp@)
        }
    {
        i -= 1;
        result.push(temp[i]);
    }
    
    proof {
        Int2Str_valid(n);
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
    // Convert inputs to u64 values
    let x_val = str_to_u64(sx);
    let y_val = str_to_u64(sy);
    let z_val = str_to_u64(sz);
    
    // Perform modular exponentiation
    let mut result: u64 = 1;
    let mut base = x_val % z_val;
    let mut exp = y_val;
    
    while exp > 0
        invariant {
            z_val > 1 &&
            base < z_val &&
            result < z_val
        }
    {
        if exp % 2 == 1 {
            result = mod_mul(result, base, z_val);
        }
        if exp > 1 {
            base = mod_mul(base, base, z_val);
        }
        exp = exp / 2;
    }
    
    // Convert result back to binary string
    u64_to_str(result)
}
// </vc-code>

fn main() {}
}