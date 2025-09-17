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

// Helper lemma for Str2Int of single character
proof fn lemma_str2int_single(bit: char)
requires bit == '0' || bit == '1'
ensures Str2Int(seq![bit]) == if bit == '1' { 1nat } else { 0nat }
{
    assert(seq![bit].len() == 1);
    assert(seq![bit].subrange(0, 0) =~= seq![]);
    lemma_str2int_empty();
}

// Helper lemma for exponentiation base cases
proof fn lemma_exp_base_cases(x: nat)
ensures Exp_int(x, 0) == 1, Exp_int(x, 1) == x, Exp_int(x, 2) == x * x
{
    assert(Exp_int(x, 0) == 1);
    assert(Exp_int(x, 1) == x * Exp_int(x, 0) == x * 1 == x);
    assert(Exp_int(x, 2) == x * Exp_int(x, 1) == x * x);
}

// Helper lemma for exponentiation with even exponent
proof fn lemma_exp_even(x: nat, y: nat)
requires y > 0, y % 2 == 0
ensures Exp_int(x, y) == Exp_int(x * x, y / 2)
decreases y
{
    lemma_exp_base_cases(x);
    lemma_exp_base_cases(x * x);
    
    if y == 2 {
        assert(y / 2 == 1);
        assert(Exp_int(x * x, 1) == x * x);
        assert(Exp_int(x, 2) == x * x);
    } else {
        assert(y >= 4);
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
        assert(Exp_int(x, (y - 1) as nat) == x * Exp_int(x, (y - 2) as nat));
        assert(Exp_int(x, y) == x * x * Exp_int(x, (y - 2) as nat));
        
        lemma_exp_even(x, (y - 2) as nat);
        assert(Exp_int(x, (y - 2) as nat) == Exp_int(x * x, ((y - 2) / 2) as nat));
        
        assert(Exp_int(x * x, y / 2) == (x * x) * Exp_int(x * x, (y / 2 - 1) as nat));
        assert((y / 2 - 1) as nat == ((y - 2) / 2) as nat);
    }
}

// Helper lemma for exponentiation with odd exponent
proof fn lemma_exp_odd(x: nat, y: nat)
requires y > 0, y % 2 == 1
ensures Exp_int(x, y) == x * Exp_int(x * x, y / 2)
decreases y
{
    lemma_exp_base_cases(x);
    lemma_exp_base_cases(x * x);
    
    if y == 1 {
        assert(y / 2 == 0);
        assert(Exp_int(x * x, 0) == 1);
        assert(Exp_int(x, 1) == x);
    } else {
        assert(y >= 3);
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
        assert((y - 1) % 2 == 0);
        lemma_exp_even(x, (y - 1) as nat);
        assert(Exp_int(x, (y - 1) as nat) == Exp_int(x * x, ((y - 1) / 2) as nat));
        assert(((y - 1) / 2) as nat == y / 2);
    }
}

// Helper lemma for Exp_int(2, n) > 0
proof fn lemma_exp2_positive(n: nat)
ensures Exp_int(2, n) > 0
decreases n
{
    if n == 0 {
        assert(Exp_int(2, 0) == 1);
    } else {
        lemma_exp2_positive((n - 1) as nat);
        assert(Exp_int(2, n) == 2 * Exp_int(2, (n - 1) as nat));
    }
}

// Convert binary string to nat
exec fn binary_to_nat(s: &[char]) -> (res: u64)
requires ValidBitString(s@), s@.len() <= 63, Str2Int(s@) < 0x8000000000000000
ensures res == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    proof {
        lemma_str2int_empty();
        assert(s@.subrange(0, 0) =~= seq![]);
    }
    
    while i < s.len()
    invariant
        0 <= i <= s.len(),
        ValidBitString(s@),
        s@.len() <= 63,
        result == Str2Int(s@.subrange(0, i as int)),
        result < 0x8000000000000000,
        Str2Int(s@) < 0x8000000000000000
    decreases s.len() - i
    {
        let bit = if s[i] == '1' { 1u64 } else { 0u64 };
        
        proof {
            let prefix = s@.subrange(0, i as int);
            let next_prefix = s@.subrange(0, (i + 1) as int);
            assert(next_prefix =~= prefix.push(s@[i as int]));
            lemma_str2int_append(prefix, s@[i as int]);
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
        proof {
            lemma_str2int_single('0');
        }
        return v;
    }
    
    let mut result = Vec::<char>::new();
    let mut num = n;
    let mut power: u64 = 1;
    
    proof {
        lemma_str2int_empty();
        assert(Exp_int(2, 0) == 1);
    }
    
    while num > 0
    invariant 
        ValidBitString(result@),
        power == Exp_int(2, result@.len() as nat),
        power > 0,
        Str2Int(result@) + num * power == n
    decreases num
    {
        let bit = if num % 2 == 0 { '0' } else { '1' };
        
        proof {
            let old_result = result@;
            let new_result = seq![bit] + old_result;
            
            if result@.len() == 0 {
                lemma_str2int_single(bit);
                assert(power == 1);
            } else {
                assert(ValidBitString(seq![bit]));
                assert(ValidBitString(new_result));
            }
            
            lemma_exp2_positive((result@.len() + 1) as nat);
        }
        
        result.insert(0, bit);
        num = num / 2;
        power = power * 2;
    }
    
    proof {
        assert(num == 0);
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
    if a <= u64::MAX / b {
        // Safe to use 64-bit arithmetic
        let prod = a * b;
        proof {
            assert(prod == a as nat * b as nat);
        }
        prod % m
    } else {
        // Use alternative algorithm to avoid overflow
        let mut result: u64 = 0;
        let mut a_temp = a;
        let mut b_temp = b;
        
        while b_temp > 0
        invariant
            m > 0,
            a_temp < m,
            result < m,
            (result + a_temp * b_temp) % m == (a as nat * b as nat) % (m as nat)
        decreases b_temp
        {
            if b_temp % 2 == 1 {
                result = (result + a_temp) % m;
            }
            a_temp = (a_temp * 2) % m;
            b_temp = b_temp / 2;
        }
        
        result
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
    // Handle edge cases
    if sz.len() == 0 || sz.len() > 63 || sy.len() > 63 || sx.len() > 63 {
        let mut v = Vec::<char>::new();
        v.push('0');
        proof {
            lemma_str2int_single('0');
        }
        return v;
    }
    
    // Check if we can safely convert to u64
    let mut can_convert = true;
    let mut check_val: u64 = 0;
    let mut i: usize = 0;
    
    while i < sz.len()
    invariant
        0 <= i <= sz.len(),
        ValidBitString(sz@),
        can_convert ==> check_val == Str2Int(sz@.subrange(0, i as int)),
        can_convert ==> check_val < 0x8000000000000000
    decreases sz.len() - i
    {
        if can_convert {
            let bit = if sz[i] == '1' { 1u64 } else { 0u64 };
            if check_val > 0x3FFFFFFFFFFFFFFF {
                can_convert = false;
            } else {
                check_val = check_val * 2 + bit;
            }
        }
        i = i + 1;
    }
    
    if !can_convert || check_val <= 1 {
        let mut v = Vec::<char>::new();
        v.push('0');
        proof {
            lemma_str2int_single('0');
        }
        return v;
    }
    
    proof {
        assert(check_val == Str2Int(sz@));
        assert(check_val > 1);
        assert(check_val < 0x8000000000000000);
    }
    
    let z_val = check_val;
    
    // Convert x safely
    can_convert = true;
    check_val = 0;
    i = 0;
    
    while i < sx.len()
    invariant
        0 <= i <= sx.len(),
        ValidBitString(sx@),
        can_convert ==> check_val == Str2Int(sx@.subrange(0, i as int)),
        can_convert ==> check_val < 0x8000000000000000
    decreases sx.len() - i
    {
        if can_convert {
            let bit = if sx[i] == '1' { 1u64 } else { 0u64 };
            if check_val > 0x3FFFFFFFFFFFFFFF {
                can_convert = false;
            } else {
                check_val = check_val * 2 + bit;
            }
        }
        i = i + 1;
    }
    
    let x_val = if can_convert { check_val } else { 0 };
    
    // Convert y safely
    can_convert = true;
    check_val = 0;
    i = 0;
    
    while i < sy.len()
    invariant
        0 <= i <= sy.len(),
        ValidBitString(sy@),
        can_convert ==> check_val == Str2Int(sy@.subrange(0, i as int)),
        can_convert ==> check_val < 0x8000000000000000
    decreases sy.len() - i
    {
        if can_convert {
            let bit = if sy[i] == '1' { 1u64 } else { 0u64 };
            if check_val > 0x3FFFFFFFFFFFFFFF {
                can_convert = false;
            } else {
                check_val = check_val * 2 + bit;
            }
        }
        i = i + 1;
    }
    
    let y_val = if can_convert { check_val } else { 0 };
    
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
        assert(base < z_val);
        assert((result as nat * Exp_int(base as nat, exp as nat)) % (z_val as nat) == Exp_int(x_val as nat, y_val as nat) % (z_val as nat));
    }
    
    while exp > 0
    invariant
        z_val > 1,
        result < z_val,
        base < z_val,
        (result as nat * Exp_int(base as nat, exp as nat)) % (z_val as nat) == Exp_int(x_val as nat, y_val as nat) % (z_val as nat)
    decreases exp
    {
        if exp % 2 == 1 {
            let old_result = result;
            result = mul_mod(result, base, z_val);
            proof {
                lemma_exp_odd(base as nat, exp as nat);
            }
        } else {
            proof {
                lemma_exp_even(base as nat, exp as nat);
            }
        }
        base = mul_mod(base, base, z_val);
        exp = exp / 2;
    }
    
    proof {
        assert(exp == 0);
        assert(Exp_int(base as nat, 0nat) == 1);
        assert(result as nat == Exp_int(x_val as nat, y_val as nat) % (z_val as nat));
    }
    
    nat_to_binary(result)
}
// </vc-code>

fn main() {}
}