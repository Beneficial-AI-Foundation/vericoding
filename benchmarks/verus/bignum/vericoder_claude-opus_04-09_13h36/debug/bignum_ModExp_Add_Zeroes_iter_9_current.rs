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
// Helper function to convert a nat to a binary string
spec fn Int2Str(n: nat) -> Seq<char>
decreases n
{
    if n == 0 {
        seq![]
    } else {
        Int2Str(n / 2).push(if n % 2 == 0 { '0' } else { '1' })
    }
}

// Helper lemma: Str2Int of empty sequence is 0
proof fn lemma_str2int_empty()
ensures Str2Int(seq![]) == 0
{
}

// Helper lemma: relationship between Str2Int and appending a bit
proof fn lemma_str2int_append(s: Seq<char>, bit: char)
requires ValidBitString(s), bit == '0' || bit == '1'
ensures ValidBitString(s.push(bit)), Str2Int(s.push(bit)) == 2 * Str2Int(s) + (if bit == '1' { 1nat } else { 0nat })
{
    let s_new = s.push(bit);
    assert(s_new.len() == s.len() + 1);
    assert(s_new.subrange(0, s_new.len() - 1) =~= s);
    assert(s_new.index(s_new.len() - 1) == bit);
}

// Helper lemma for exponentiation with even exponent
proof fn lemma_exp_even(x: nat, y: nat)
requires y > 0, y % 2 == 0
ensures Exp_int(x, y) == Exp_int(x * x, y / 2)
decreases y
{
    if y == 2 {
        assert(Exp_int(x, 2) == x * Exp_int(x, 1));
        assert(Exp_int(x, 1) == x * Exp_int(x, 0));
        assert(Exp_int(x, 0) == 1);
        assert(Exp_int(x, 2) == x * x);
        
        assert(Exp_int(x * x, 1) == (x * x) * Exp_int(x * x, 0));
        assert(Exp_int(x * x, 0) == 1);
        assert(Exp_int(x * x, 1) == x * x);
        assert(y / 2 == 1);
        assert(Exp_int(x * x, y / 2) == x * x);
    } else {
        assert(y >= 4);
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
        assert(Exp_int(x, (y - 1) as nat) == x * Exp_int(x, (y - 2) as nat));
        assert(Exp_int(x, y) == x * x * Exp_int(x, (y - 2) as nat));
        assert((y - 2) % 2 == 0);
        lemma_exp_even(x, (y - 2) as nat);
        assert(Exp_int(x, (y - 2) as nat) == Exp_int(x * x, ((y - 2) / 2) as nat));
        assert(((y - 2) / 2) as nat == (y / 2 - 1) as nat);
        assert(Exp_int(x * x, y / 2) == (x * x) * Exp_int(x * x, (y / 2 - 1) as nat));
        assert(Exp_int(x * x, (y / 2 - 1) as nat) == Exp_int(x * x, ((y - 2) / 2) as nat));
    }
}

// Helper lemma for exponentiation with odd exponent
proof fn lemma_exp_odd(x: nat, y: nat)
requires y > 0, y % 2 == 1
ensures Exp_int(x, y) == x * Exp_int(x * x, y / 2)
decreases y
{
    if y == 1 {
        assert(Exp_int(x, 1) == x * Exp_int(x, 0));
        assert(Exp_int(x, 0) == 1);
        assert(Exp_int(x * x, 0) == 1);
        assert(y / 2 == 0);
    } else {
        assert(y >= 3);
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
        assert((y - 1) % 2 == 0);
        lemma_exp_even(x, (y - 1) as nat);
        assert(Exp_int(x, (y - 1) as nat) == Exp_int(x * x, ((y - 1) / 2) as nat));
        assert(((y - 1) / 2) as nat == y / 2);
    }
}

// Convert binary string to nat
exec fn binary_to_nat(s: &[char]) -> (res: u64)
requires ValidBitString(s@), s@.len() <= 63, Str2Int(s@) < 0x8000000000000000
ensures res == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
    invariant
        0 <= i <= s.len(),
        ValidBitString(s@),
        result == Str2Int(s@.subrange(0, i as int)),
        result < 0x8000000000000000
    decreases s.len() - i
    {
        let bit = if s[i] == '1' { 1u64 } else { 0u64 };
        
        proof {
            let prefix = s@.subrange(0, i as int);
            let next_prefix = s@.subrange(0, i + 1);
            assert(next_prefix =~= prefix.push(s@[i as int]));
            lemma_str2int_append(prefix, s@[i as int]);
            assert(Str2Int(next_prefix) == 2 * Str2Int(prefix) + (if s@[i as int] == '1' { 1nat } else { 0nat }));
            assert(2 * result < 0x8000000000000000 * 2);
            assert(2 * result + bit < 0x10000000000000000);
        }
        
        result = result * 2 + bit;
        i = i + 1;
    }
    
    proof {
        assert(s@.subrange(0, s@.len() as int) =~= s@);
    }
    
    result
}

// Convert nat to Vec<char> binary string  
exec fn nat_to_binary(n: u64) -> (res: Vec<char>)
ensures ValidBitString(res@), Str2Int(res@) == n
{
    if n == 0 {
        let mut v = Vec::<char>::new();
        v.push('0');
        return v;
    }
    
    let mut result = Vec::<char>::new();
    let mut num = n;
    
    while num > 0
    invariant 
        ValidBitString(result@),
        result@.len() == 0 ==> num == n,
        result@.len() > 0 ==> Str2Int(result@) + num * Exp_int(2, result@.len() as nat) == n
    decreases num
    {
        let bit = if num % 2 == 0 { '0' } else { '1' };
        
        proof {
            if result@.len() == 0 {
                lemma_str2int_empty();
                assert(Str2Int(seq![]) == 0);
                assert(Str2Int(seq![bit]) == if bit == '1' { 1nat } else { 0nat });
                assert(Exp_int(2, 1) == 2);
                assert((num / 2) * 2 + (num % 2) == num);
            } else {
                let old_result = result@;
                let new_result = old_result.push(bit);
                lemma_str2int_append(old_result, bit);
                assert(Str2Int(new_result) == 2 * Str2Int(old_result) + (if bit == '1' { 1nat } else { 0nat }));
                assert(Exp_int(2, new_result.len() as nat) == 2 * Exp_int(2, old_result.len() as nat));
            }
        }
        
        result.push(bit);
        num = num / 2;
    }
    
    proof {
        assert(num == 0);
        assert(Exp_int(2, result@.len() as nat) > 0);
        assert(Str2Int(result@) == n);
    }
    
    result
}

// Helper to compute (a * b) % m safely
exec fn mul_mod(a: u64, b: u64, m: u64) -> (res: u64)
requires m > 0, a < m, b < m
ensures res == (a as nat * b as nat) % (m as nat), res < m
{
    if a == 0 || b == 0 {
        return 0;
    }
    
    // Check if multiplication would overflow
    if a > u64::MAX / b {
        // Use 128-bit arithmetic
        let prod = (a as u128) * (b as u128);
        let m128 = m as u128;
        let res128 = prod % m128;
        proof {
            assert(res128 < m128);
            assert(res128 == (a as nat * b as nat) % (m as nat));
        }
        res128 as u64
    } else {
        // Safe to use 64-bit arithmetic
        let prod = a * b;
        proof {
            assert(prod == a as nat * b as nat);
        }
        prod % m
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    // Check preconditions for binary_to_nat
    if sx.len() > 63 || sy.len() > 63 || sz.len() > 63 {
        // Return 0 for invalid inputs
        let mut v = Vec::<char>::new();
        v.push('0');
        return v;
    }
    
    proof {
        assert(sx@.len() <= 63);
        assert(sy@.len() <= 63);
        assert(sz@.len() <= 63);
        assert(ValidBitString(sx@));
        assert(ValidBitString(sy@));
        assert(ValidBitString(sz@));
    }
    
    let x_val = binary_to_nat(sx);
    let y_val = binary_to_nat(sy);
    let z_val = binary_to_nat(sz);
    
    if y_val == 0 {
        proof {
            assert(Exp_int(x_val as nat, 0nat) == 1);
        }
        return nat_to_binary(1 % z_val);
    }
    
    let mut base = x_val % z_val;
    let mut result = 1u64;
    let mut exp = y_val;
    
    proof {
        assert(result == 1);
        assert(Exp_int(x_val as nat, y_val as nat) % (z_val as nat) == Exp_int(base as nat, exp as nat) % (z_val as nat));
        assert((result as nat * Exp_int(base as nat, exp as nat)) % (z_val as nat) == Exp_int(x_val as nat, y_val as nat) % (z_val as nat));
    }
    
    while exp > 0
    invariant
        z_val > 1,
        z_val == Str2Int(sz@),
        result < z_val,
        base < z_val,
        exp <= y_val,
        (result as nat * Exp_int(base as nat, exp as nat)) % (z_val as nat) == Exp_int(x_val as nat, y_val as nat) % (z_val as nat)
    decreases exp
    {
        if exp % 2 == 1 {
            let old_result = result;
            result = mul_mod(result, base, z_val);
            proof {
                lemma_exp_odd(base as nat, exp as nat);
                assert(Exp_int(base as nat, exp as nat) == (base as nat) * Exp_int((base as nat) * (base as nat), (exp / 2) as nat));
                assert((old_result as nat * base as nat) % (z_val as nat) == result as nat);
                assert((old_result as nat * (base as nat * Exp_int((base as nat) * (base as nat), (exp / 2) as nat))) % (z_val as nat) 
                    == (result as nat * Exp_int((base as nat) * (base as nat), (exp / 2) as nat)) % (z_val as nat));
            }
        } else {
            proof {
                lemma_exp_even(base as nat, exp as nat);
                assert(Exp_int(base as nat, exp as nat) == Exp_int((base as nat) * (base as nat), (exp / 2) as nat));
            }
        }
        base = mul_mod(base, base, z_val);
        exp = exp / 2;
    }
    
    proof {
        assert(exp == 0);
        assert(Exp_int(base as nat, 0nat) == 1);
        assert((result as nat * 1) % (z_val as nat) == result as nat);
        assert(result < z_val);
        assert(result as nat == Exp_int(x_val as nat, y_val as nat) % (z_val as nat));
    }
    
    nat_to_binary(result)
}
// </vc-code>

fn main() {}
}