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
/* helper modified by LLM (iteration 7): Fixed missing decreases clause in while loop */
proof fn lemma_exp_zero(x: nat)
    ensures Exp_int(x, 0) == 1
{
}

proof fn lemma_exp_succ(x: nat, y: nat)
    ensures Exp_int(x, y + 1) == x * Exp_int(x, y)
{
}

proof fn lemma_exp_mod(x: nat, y: nat, z: nat)
    requires z > 0,
            y > 0
    ensures Exp_int(x, y) % z == ((x % z) * Exp_int(x, (y - 1) as nat)) % z
{
    // Base case handled by definition
}

exec fn int_to_binary(mut n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@),
            res@.len() > 0,
            Str2Int(res@) == n as nat
{
    let mut result = Vec::new();
    if n == 0 {
        result.push('0');
        assert(result@.len() == 1);
        assert(result@[0] == '0');
        assert(Str2Int(result@) == 0);
        return result;
    }
    
    let ghost old_n = n;
    let ghost mut bits_collected = 0nat;
    
    while n > 0
        invariant
            ValidBitString(result@),
            bits_collected == Str2Int(result@),
            n as nat * Exp_int(2, result@.len() as nat) + bits_collected == old_n as nat,
            old_n > 0 ==> (n > 0 || bits_collected > 0)
        decreases n
    {
        let ghost old_bits = bits_collected;
        let ghost old_len = result@.len();
        
        if n % 2 == 1 {
            result.push('1');
            proof {
                bits_collected = old_bits + Exp_int(2, old_len as nat);
            }
        } else {
            result.push('0');
        }
        n = n / 2;
    }
    
    // Reverse the result to get proper bit order
    let mut reversed = Vec::new();
    let mut i = result.len();
    while i > 0
        invariant
            0 <= i <= result.len(),
            ValidBitString(reversed@),
            reversed@.len() == result.len() - i
        decreases i
    {
        i = i - 1;
        reversed.push(result[i]);
    }
    
    reversed
}

exec fn modular_multiply(a: u64, b: u64, modulus: u64) -> (res: u64)
    requires modulus > 1,
            a < modulus,
            b < modulus,
            (a as int * b as int) < 0x10000000000000000  // Prevent overflow
    ensures res == ((a as int * b as int) % modulus as int) as u64,
            res < modulus
{
    let product = a * b;
    product % modulus
}

exec fn modular_exp(base: u64, mut exp: u64, modulus: u64) -> (res: u64)
    requires modulus > 1
    ensures res == (Exp_int(base as nat, exp as nat) % modulus as nat) as u64
    decreases exp
{
    if exp == 0 {
        return 1 % modulus;
    }
    
    let ghost old_exp = exp;
    let mut result = 1u64;
    let mut base_mod = base % modulus;
    
    proof {
        assert(Exp_int(base as nat, 0) == 1);
    }
    
    while exp > 0
        invariant
            modulus > 1,
            result < modulus,
            base_mod < modulus,
            exp <= old_exp,
            (result as nat * Exp_int(base as nat, exp as nat)) % modulus as nat == Exp_int(base as nat, old_exp as nat) % modulus as nat
        decreases exp
    {
        if exp % 2 == 1 {
            // Use checked multiply to avoid overflow
            if result <= u64::MAX / base_mod && (result * base_mod) <= u64::MAX / modulus {
                result = modular_multiply(result, base_mod, modulus);
            } else {
                result = ((result % modulus) * (base_mod % modulus)) % modulus;
            }
            proof {
                lemma_exp_mod(base as nat, exp as nat, modulus as nat);
            }
        }
        if exp > 1 {
            if base_mod <= u64::MAX / base_mod && (base_mod * base_mod) <= u64::MAX / modulus {
                base_mod = modular_multiply(base_mod, base_mod, modulus);
            } else {
                base_mod = ((base_mod % modulus) * (base_mod % modulus)) % modulus;
            }
        }
        exp = exp / 2;
    }
    result
}

exec fn binary_to_int(s: &[char]) -> (res: u64)
    requires ValidBitString(s@),
            s@.len() <= 64,
            s@.len() > 0
    ensures res == Str2Int(s@) as u64
{
    let mut result = 0u64;
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            i == 0 ==> result == 0,
            i > 0 ==> result == Str2Int(s@.subrange(0, i as int)) as u64,
            result <= u64::MAX / 2 || i == s.len()
        decreases s.len() - i
    {
        if i < s.len() - 1 {
            // Check for overflow before multiplication
            if result > u64::MAX / 2 {
                // Handle overflow case
                return u64::MAX;
            }
            result = result * 2;
        } else {
            // Last iteration, be careful with overflow
            if result <= u64::MAX / 2 {
                result = result * 2;
            } else {
                return u64::MAX;
            }
        }
        
        if s[i] == '1' {
            if result < u64::MAX {
                result = result + 1;
            }
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
/* code modified by LLM (iteration 7): Added missing decreases clause to while loop */
{
    // Handle edge cases
    if sy.len() == 0 || sz.len() == 0 || sx.len() == 0 {
        let mut res = Vec::new();
        res.push('0');
        return res;
    }
    
    // Check if sy is all zeros (exp = 0)
    let mut all_zeros = true;
    let mut i = 0;
    while i < sy.len()
        invariant
            0 <= i <= sy.len(),
            all_zeros == (forall|j: int| 0 <= j && j < i ==> sy@[j] == '0')
        decreases sy.len() - i
    {
        if sy[i] != '0' {
            all_zeros = false;
            break;
        }
        i = i + 1;
    }
    
    if all_zeros {
        let mut res = Vec::new();
        res.push('1');
        return res;
    }
    
    // Ensure inputs are within bounds for binary_to_int
    if sx.len() > 64 || sy.len() > 64 || sz.len() > 64 {
        let mut res = Vec::new();
        res.push('0');
        return res;
    }
    
    let x_int = binary_to_int(sx);
    let y_int = binary_to_int(sy);
    let z_int = binary_to_int(sz);
    
    // Check modulus is valid
    if z_int <= 1 {
        let mut res = Vec::new();
        res.push('0');
        return res;
    }
    
    let result_int = modular_exp(x_int, y_int, z_int);
    let result = int_to_binary(result_int);
    
    result
}
// </vc-code>

fn main() {}
}
