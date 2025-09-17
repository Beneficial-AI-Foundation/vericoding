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
    if exp == 2 {
        assert(Exp_int(base, 2) == base * Exp_int(base, 1));
        assert(Exp_int(base, 1) == base * Exp_int(base, 0));
        assert(Exp_int(base, 0) == 1);
        assert(Exp_int(base, 1) == base * 1);
        assert(Exp_int(base, 1) == base);
        assert(Exp_int(base, 2) == base * base);
        assert(exp / 2 == 1);
        assert(Exp_int(base, exp / 2) == base);
        assert(Exp_int(base, exp / 2) * Exp_int(base, exp / 2) == base * base);
    } else {
        let half_exp = exp / 2;
        assert(exp == 2 * half_exp);
        if half_exp > 0 && half_exp % 2 == 0 {
            lemma_exp_even(base, half_exp);
        }
        
        // Prove by induction on the structure of exp
        assert(Exp_int(base, exp) == base * Exp_int(base, (exp - 1) as nat));
        assert(Exp_int(base, (exp - 1) as nat) == base * Exp_int(base, ((exp - 1) - 1) as nat));
        
        // Since exp is even and > 2, we can write it as 2*k for some k > 1
        let k = exp / 2;
        assert(exp == 2 * k);
        
        // Use the mathematical property that x^(2k) = (x^k)^2
        lemma_exp_property(base, k);
    }
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
        assert(Exp_int(base, 2 * k) == base * Exp_int(base, (2 * k - 1) as nat));
        assert(2 * k - 1 == 2 * (k - 1) + 1);
        assert(Exp_int(base, (2 * k - 1) as nat) == base * Exp_int(base, (2 * (k - 1)) as nat));
        assert(Exp_int(base, (2 * (k - 1)) as nat) == Exp_int(base, (k - 1) as nat) * Exp_int(base, (k - 1) as nat));
        assert(Exp_int(base, k) == base * Exp_int(base, (k - 1) as nat));
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
        assert(Exp_int(base, 0) % modulus == 1nat % modulus);
    } else if exp % 2 == 0 {
        lemma_pow_mod_correct(base, exp / 2, modulus);
        lemma_exp_even(base, exp);
        let half_pow = pow_mod(base, exp / 2, modulus);
        assert(half_pow == Exp_int(base, exp / 2) % modulus);
        assert(Exp_int(base, exp) == Exp_int(base, exp / 2) * Exp_int(base, exp / 2));
        assert((half_pow * half_pow) % modulus == (Exp_int(base, exp / 2) * Exp_int(base, exp / 2)) % modulus);
    } else {
        lemma_pow_mod_correct(base, (exp - 1) as nat, modulus);
        assert(pow_mod(base, (exp - 1) as nat, modulus) == Exp_int(base, (exp - 1) as nat) % modulus);
        assert(Exp_int(base, exp) == base * Exp_int(base, (exp - 1) as nat));
        assert((base * pow_mod(base, (exp - 1) as nat, modulus)) % modulus == 
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
        assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }));
        assert(Str2Int(s.subrange(0, s.len() as int - 1)) < 0x8000_0000_0000_0000nat);
        if s.len() == 1 {
            assert(Str2Int(s) <= 1);
        } else {
            assert(Str2Int(s) <= 2 * (0x8000_0000_0000_0000nat - 1) + 1);
            assert(Str2Int(s) < 0x8000_0000_0000_0000nat * 2);
        }
    }
}

proof fn lemma_str2int_subrange(s: Seq<char>, i: int)
    requires ValidBitString(s), 0 <= i <= s.len()
    ensures ValidBitString(s.subrange(0, i))
    decreases i
{
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
        proof { lemma_str2int_subrange(s@, i as int); }
        
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        i += 1;
        
        assert(result as nat == Str2Int(s@.subrange(0, i as int)));
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
            result as nat == pow_mod(base_val as nat, (exp_val - exp) as nat, mod_val as nat),
            base as nat == pow_mod(base_val as nat, (exp_val - exp) as nat * 2, mod_val as nat) % (mod_val as nat)
        decreases exp
    {
        if exp % 2 == 1 {
            result = (result * base) % mod_val;
        }
        base = (base * base) % mod_val;
        exp = exp / 2;
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