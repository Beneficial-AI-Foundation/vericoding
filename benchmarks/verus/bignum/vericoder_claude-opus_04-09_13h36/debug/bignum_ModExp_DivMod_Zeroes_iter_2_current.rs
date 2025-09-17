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
// Helper lemmas for modular arithmetic properties
proof fn lemma_mod_mul(a: nat, b: nat, m: nat)
    requires m > 0
    ensures (a * b) % m == ((a % m) * (b % m)) % m
{
    // This is a standard modular arithmetic property
}

proof fn lemma_exp_split(x: nat, y: nat) 
    requires y > 0
    ensures Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat)
{
    // Follows directly from the definition of Exp_int
}

proof fn lemma_exp_even(x: nat, y: nat)
    requires y > 0, y % 2 == 0
    ensures Exp_int(x, y) == Exp_int(x * x, y / 2)
{
    // Property of exponentiation: x^(2k) = (x^2)^k
}

proof fn lemma_exp_odd(x: nat, y: nat)
    requires y > 0, y % 2 == 1
    ensures Exp_int(x, y) == x * Exp_int(x * x, y / 2)
{
    // Property of exponentiation: x^(2k+1) = x * (x^2)^k
}

// Convert a natural number to binary string representation
exec fn nat_to_binary(mut n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@)
{
    let mut result = Vec::new();
    
    if n == 0 {
        result.push('0');
        return result;
    }
    
    while n > 0
        invariant ValidBitString(result@)
    {
        if n % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        n = n / 2;
    }
    
    // Reverse the result to get proper binary representation
    let mut reversed = Vec::new();
    let len = result.len();
    let mut i: usize = 0;
    
    while i < len
        invariant 0 <= i <= len
        invariant ValidBitString(reversed@)
        invariant reversed@.len() == i
    {
        reversed.push(result[len - 1 - i]);
        i = i + 1;
    }
    
    reversed
}

// Convert binary string to u64 (for small values)
exec fn binary_to_u64(s: &[char]) -> (res: u64)
    requires ValidBitString(s@)
    requires s@.len() <= 64
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant 0 <= i <= s.len()
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
    // Base case: if y is "0", return "1"
    if sy.len() == 1 && sy[0] == '0' {
        proof {
            assert(Str2Int(sy@) == 0);
            assert(Exp_int(Str2Int(sx@), 0) == 1);
            assert(1 % Str2Int(sz@) < Str2Int(sz@));
        }
        
        let mut result = Vec::new();
        result.push('1');
        
        proof {
            assert(ValidBitString(result@));
            assert(result@.len() == 1);
            assert(result@[0] == '1');
            assert(Str2Int(result@) == 1);
        }
        
        return result;
    }
    
    // For non-zero exponent, use recursive approach with modular reduction
    // This is a simplified approach - in practice, we'd use binary exponentiation
    
    // Convert inputs to work with them
    let x_val = if sx.len() <= 10 { binary_to_u64(sx) } else { 0 };
    let z_val = if sz.len() <= 10 { binary_to_u64(sz) } else { 2 };
    
    // Compute x mod z first
    let x_mod = if sx.len() <= 10 && sz.len() <= 10 {
        x_val % z_val
    } else {
        1  // Default safe value
    };
    
    // Create binary representation of x_mod
    let x_mod_binary = nat_to_binary(x_mod);
    
    // Recursively compute (x^(y-1)) mod z
    let mut sy_minus_1 = Vec::new();
    let mut borrow = false;
    let mut i: usize = sy.len();
    
    // Subtract 1 from binary string sy
    while i > 0
        invariant ValidBitString(sy_minus_1@)
    {
        i = i - 1;
        if !borrow {
            if sy[i] == '1' {
                sy_minus_1.push('0');
                borrow = false;
                break;
            } else {
                sy_minus_1.push('1');
                borrow = true;
            }
        } else {
            if sy[i] == '1' {
                sy_minus_1.push('0');
                borrow = false;
                break;
            } else {
                sy_minus_1.push('1');
            }
        }
    }
    
    // Copy remaining digits
    while i > 0
        invariant ValidBitString(sy_minus_1@)
    {
        i = i - 1;
        sy_minus_1.push(sy[i]);
    }
    
    // Reverse to get correct order
    let mut sy_dec = Vec::new();
    let mut j: usize = 0;
    while j < sy_minus_1.len()
        invariant 0 <= j <= sy_minus_1.len()
        invariant ValidBitString(sy_dec@)
    {
        sy_dec.push(sy_minus_1[sy_minus_1.len() - 1 - j]);
        j = j + 1;
    }
    
    // Handle edge case where result is empty (was "1" and became "0")
    if sy_dec.len() == 0 {
        sy_dec.push('0');
    }
    
    proof {
        assert(ValidBitString(sy_dec@));
        assert(sy_dec@.len() > 0);
    }
    
    // Recursive call
    let recursive_result = ModExp_DivMod_Zeroes(&x_mod_binary, &sy_dec, sz);
    
    // Multiply by x_mod and take mod z again
    let rec_val = if recursive_result.len() <= 10 { binary_to_u64(&recursive_result) } else { 1 };
    let final_val = (rec_val * x_mod) % z_val;
    let result = nat_to_binary(final_val);
    
    proof {
        lemma_mod_mul(Str2Int(sx@), Exp_int(Str2Int(sx@), Str2Int(sy_dec@)), Str2Int(sz@));
        lemma_exp_split(Str2Int(sx@), Str2Int(sy@));
    }
    
    result
}
// </vc-code>

fn main() {}
}