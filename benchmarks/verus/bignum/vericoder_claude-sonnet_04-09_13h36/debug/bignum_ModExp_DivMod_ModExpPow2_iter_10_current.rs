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
        let half_pow = pow_mod(base, exp / 2, modulus);
        (half_pow * half_pow) % modulus
    } else {
        (base * pow_mod(base, (exp - 1) as nat, modulus)) % modulus
    }
}

proof fn lemma_exp_even(base: nat, exp: nat)
    requires exp > 0, exp % 2 == 0
    ensures Exp_int(base, exp) == Exp_int(base, exp / 2) * Exp_int(base, exp / 2)
    decreases exp
{
    lemma_exp_property(base, exp / 2);
}

proof fn lemma_exp_property(base: nat, k: nat)
    ensures Exp_int(base, 2 * k) == Exp_int(base, k) * Exp_int(base, k)
    decreases k
{
    if k == 0 {
        assert(Exp_int(base, 0) == 1);
        assert(Exp_int(base, 2 * 0) == Exp_int(base, 0) == 1);
        assert(Exp_int(base, k) * Exp_int(base, k) == 1 * 1 == 1);
    } else {
        lemma_exp_property(base, (k - 1) as nat);
        
        // Prove the general case: x^(2k) = x^k * x^k
        // We know x^(2k) = x * x^(2k-1)
        assert(Exp_int(base, 2 * k) == base * Exp_int(base, (2 * k - 1) as nat));
        
        // And x^(2k-1) = x * x^(2k-2) = x * x^(2(k-1))
        assert((2 * k - 1) as nat == 1 + (2 * (k - 1)) as nat);
        assert(Exp_int(base, (2 * k - 1) as nat) == base * Exp_int(base, (2 * (k - 1)) as nat));
        
        // By induction hypothesis: x^(2(k-1)) = x^(k-1) * x^(k-1)
        assert(Exp_int(base, (2 * (k - 1)) as nat) == Exp_int(base, (k - 1) as nat) * Exp_int(base, (k - 1) as nat));
        
        // So x^(2k) = x * x * x^(k-1) * x^(k-1) = (x * x^(k-1)) * (x * x^(k-1)) = x^k * x^k
        assert(Exp_int(base, k) == base * Exp_int(base, (k - 1) as nat));
        assert(Exp_int(base, 2 * k) == base * base * Exp_int(base, (k - 1) as nat) * Exp_int(base, (k - 1) as nat));
        assert(Exp_int(base, 2 * k) == Exp_int(base, k) * Exp_int(base, k));
    }
}

proof fn lemma_pow_mod_correct(base: nat, exp: nat, modulus: nat)
    requires modulus > 0
    ensures pow_mod(base, exp, modulus) == Exp_int(base, exp) % modulus
    decreases exp
{
    if exp == 0 {
        assert(pow_mod(base, 0, modulus) == 1nat % modulus);
        assert(Exp_int(base, 0) == 1nat);
    } else if exp % 2 == 0 {
        lemma_pow_mod_correct(base, exp / 2, modulus);
        lemma_exp_even(base, exp);
        let half_pow = pow_mod(base, exp / 2, modulus);
        assert(half_pow == Exp_int(base, exp / 2) % modulus);
        assert(Exp_int(base, exp) == Exp_int(base, exp / 2) * Exp_int(base, exp / 2));
        
        // Use modular arithmetic property: (a % m) * (b % m) % m = (a * b) % m
        assert((half_pow * half_pow) % modulus == 
               ((Exp_int(base, exp / 2) % modulus) * (Exp_int(base, exp / 2) % modulus)) % modulus);
        assert(((Exp_int(base, exp / 2) % modulus) * (Exp_int(base, exp / 2) % modulus)) % modulus == 
               (Exp_int(base, exp / 2) * Exp_int(base, exp / 2)) % modulus);
    } else {
        lemma_pow_mod_correct(base, (exp - 1) as nat, modulus);
        assert(pow_mod(base, (exp - 1) as nat, modulus) == Exp_int(base, (exp - 1) as nat) % modulus);
        assert(Exp_int(base, exp) == base * Exp_int(base, (exp - 1) as nat));
        
        // Use modular arithmetic property
        assert((base * pow_mod(base, (exp - 1) as nat, modulus)) % modulus == 
               (base * (Exp_int(base, (exp - 1) as nat) % modulus)) % modulus);
        assert((base * (Exp_int(base, (exp - 1) as nat) % modulus)) % modulus == 
               (base * Exp_int(base, (exp - 1) as nat)) % modulus);
    }
}

exec fn int_to_bitstring(mut n: u64) -> (result: Vec<char>)
    ensures ValidBitString(result@)
{
    let mut temp = Vec::new();
    if n == 0 {
        temp.push('0');
        return temp;
    }
    
    while n > 0
        invariant ValidBitString(temp@)
        decreases n
    {
        if n % 2 == 0 {
            temp.push('0');
        } else {
            temp.push('1');
        }
        n = n / 2;
    }
    
    // Manual reverse
    let mut result = Vec::new();
    let mut i = temp.len();
    while i > 0
        invariant 
            ValidBitString(temp@), 
            ValidBitString(result@),
            i <= temp.len(),
            result@.len() == temp@.len() - i
        decreases i
    {
        i = i - 1;
        assert(i < temp.len());
        result.push(temp[i]);
    }
    
    result
}

proof fn lemma_str2int_bound(s: Seq<char>)
    requires ValidBitString(s), s.len() <= 63
    ensures Str2Int(s) < 0x8000_0000_0000_0000nat
    decreases s.len()
{
    if s.len() == 0 {
        assert(Str2Int(s) == 0);
    } else {
        lemma_str2int_bound(s.subrange(0, s.len() as int - 1));
        let sub = s.subrange(0, s.len() as int - 1);
        let last_bit = if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat };
        
        assert(Str2Int(s) == 2 * Str2Int(sub) + last_bit);
        assert(Str2Int(sub) < 0x8000_0000_0000_0000nat);
        
        if s.len() < 63 {
            assert(Str2Int(sub) <= 0x3FFF_FFFF_FFFF_FFFFnat);
            assert(2 * Str2Int(sub) + last_bit <= 2 * 0x3FFF_FFFF_FFFF_FFFFnat + 1);
            assert(Str2Int(s) < 0x8000_0000_0000_0000nat);
        } else {
            // s.len() == 63, so sub.len() == 62
            assert(sub.len() == 62);
            assert(Str2Int(sub) <= 0x3FFF_FFFF_FFFF_FFFFnat);
            assert(Str2Int(s) <= 2 * 0x3FFF_FFFF_FFFF_FFFFnat + 1);
            assert(Str2Int(s) < 0x8000_0000_0000_0000nat);
        }
    }
}

proof fn lemma_str2int_subrange(s: Seq<char>, i: int)
    requires ValidBitString(s), 0 <= i <= s.len()
    ensures ValidBitString(s.subrange(0, i))
    decreases i
{
}

proof fn lemma_str2int_prefix_property(s: Seq<char>, i: int)
    requires ValidBitString(s), 0 <= i < s.len()
    ensures Str2Int(s.subrange(0, i + 1)) == 2 * Str2Int(s.subrange(0, i)) + (if s.index(i) == '1' { 1nat } else { 0nat })
{
    let prefix_i = s.subrange(0, i);
    let prefix_i_plus_1 = s.subrange(0, i + 1);
    
    if i == 0 {
        assert(prefix_i.len() == 0);
        assert(Str2Int(prefix_i) == 0);
        assert(prefix_i_plus_1.len() == 1);
        assert(prefix_i_plus_1.index(0) == s.index(0));
    } else {
        assert(prefix_i_plus_1.len() == i + 1);
        assert(prefix_i_plus_1.index(i) == s.index(i));
    }
}

exec fn bitstring_to_u64(s: &[char]) -> (result: u64)
    requires ValidBitString(s@), s@.len() <= 63
    ensures result as nat == Str2Int(s@)
{
    proof { lemma_str2int_bound(s@); }
    
    let mut result: u64 = 0;
    let mut i = 0;
    
    while i < s.len()
        invariant 
            0 <= i <= s.len(),
            ValidBitString(s@),
            result as nat == Str2Int(s@.subrange(0, i as int)),
            result < 0x8000_0000_0000_0000u64
        decreases s.len() - i
    {
        proof { 
            lemma_str2int_subrange(s@, i as int);
            if i > 0 {
                lemma_str2int_prefix_property(s@, (i - 1) as int);
            }
        }
        
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        i += 1;
        
        proof {
            lemma_str2int_prefix_property(s@, (i - 1) as int);
        }
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    if sy.len() == 0 {
        return int_to_bitstring(1);
    }
    
    if sx.len() > 63 || sy.len() > 63 || sz.len() > 63 {
        return int_to_bitstring(0);
    }
    
    let base_val = bitstring_to_u64(sx);
    let exp_val = bitstring_to_u64(sy);
    let mod_val = bitstring_to_u64(sz);
    
    if mod_val <= 1 {
        return int_to_bitstring(0);
    }
    
    let mut result: u64 = 1;
    let mut base: u64 = base_val % mod_val;
    let mut exp: u64 = exp_val;
    
    while exp > 0
        invariant 
            mod_val > 1,
            result < mod_val,
            base < mod_val,
            result as nat * pow_mod(base_val as nat, exp as nat, mod_val as nat) % (mod_val as nat) == 
                pow_mod(base_val as nat, exp_val as nat, mod_val as nat)
        decreases exp
    {
        if exp % 2 == 1 {
            assert(result < mod_val && base < mod_val);
            assert(result * base < mod_val * mod_val);
            result = (result * base) % mod_val;
            exp = exp - 1;
        } else {
            assert(base < mod_val);
            assert(base * base < mod_val * mod_val);  
            base = (base * base) % mod_val;
            exp = exp / 2;
        }
    }
    
    proof {
        lemma_pow_mod_correct(Str2Int(sx@), Str2Int(sy@), Str2Int(sz@));
        assert(result as nat == pow_mod(base_val as nat, exp_val as nat, mod_val as nat));
        assert(pow_mod(base_val as nat, exp_val as nat, mod_val as nat) == 
               Exp_int(base_val as nat, exp_val as nat) % (mod_val as nat));
        assert(base_val as nat == Str2Int(sx@));
        assert(exp_val as nat == Str2Int(sy@));
        assert(mod_val as nat == Str2Int(sz@));
    }
    
    int_to_bitstring(result)
}
// </vc-code>

fn main() {}
}