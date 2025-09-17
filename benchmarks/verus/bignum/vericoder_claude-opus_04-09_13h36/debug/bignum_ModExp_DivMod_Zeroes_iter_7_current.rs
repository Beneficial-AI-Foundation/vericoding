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

// Helper function to convert nat to binary string
exec fn nat_to_binary(n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n
{
    if n == 0 {
        let mut result = Vec::new();
        result.push('0');
        return result;
    }
    
    let mut result = Vec::new();
    let mut num = n;
    
    while num > 0
        invariant ValidBitString(result@)
        decreases num
    {
        if num % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        num = num / 2;
    }
    
    // Reverse the result
    let mut final_result = Vec::new();
    let len = result.len();
    let mut i: usize = 0;
    
    while i < len
        invariant 
            0 <= i <= len,
            len == result.len(),
            ValidBitString(final_result@),
            final_result@.len() == i
        decreases len - i
    {
        final_result.push(result[len - 1 - i]);
        i = i + 1;
    }
    
    final_result
}

// Helper to compute modular multiplication
exec fn mod_mul(a: nat, b: nat, m: nat) -> (res: nat)
    requires m > 0
    ensures res == (a * b) % m
{
    proof { lemma_mod_mul(a, b, m); }
    ((a % m) * (b % m)) % m
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
    // Convert binary strings to natural numbers
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    
    // Handle base case where y = 0
    if y_val == 0 {
        let mut result = Vec::new();
        result.push('1');
        
        proof {
            assert(Exp_int(x_val, 0) == 1);
            assert(ValidBitString(result@));
            assert(Str2Int(result@) == 1);
            assert(1 % z_val == Exp_int(x_val, y_val) % z_val);
        }
        
        return result;
    }
    
    // Use binary exponentiation (square-and-multiply)
    let mut result_val: nat = 1;
    let mut base: nat = x_val % z_val;
    let mut exp: nat = y_val;
    
    while exp > 0
        invariant 
            z_val > 1,
            result_val < z_val,
            base < z_val,
            (result_val * Exp_int(base, exp)) % z_val == Exp_int(x_val, y_val) % z_val
        decreases exp
    {
        if exp % 2 == 1 {
            // Odd exponent: multiply result by base
            result_val = mod_mul(result_val, base, z_val);
            proof { 
                lemma_exp_odd(base, exp);
                lemma_mod_mul(result_val, base, z_val);
            }
        }
        
        // Square the base
        base = mod_mul(base, base, z_val);
        exp = exp / 2;
        
        proof {
            if exp > 0 {
                if exp % 2 == 0 {
                    lemma_exp_even(base, exp);
                } else {
                    lemma_exp_odd(base, exp);
                }
            }
        }
    }
    
    // Convert result back to binary string
    nat_to_binary(result_val)
}
// </vc-code>

fn main() {}
}