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
proof fn lemma_exp_properties(x: nat, y: nat)
    ensures
        y > 0 ==> Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat),
        Exp_int(x, 0) == 1,
{
}

proof fn lemma_exp_even(x: nat, y: nat)
    requires
        y > 0,
        y % 2 == 0,
    ensures
        Exp_int(x, y) == Exp_int(x * x, y / 2),
    decreases y,
{
    if y == 2 {
        assert(Exp_int(x, 2) == x * x * 1);
        assert(Exp_int(x * x, 1) == x * x * 1);
    } else {
        lemma_exp_properties(x, y);
        lemma_exp_properties(x, (y - 2) as nat);
        lemma_exp_even(x, (y - 2) as nat);
        assert(Exp_int(x, y) == x * x * Exp_int(x, (y - 2) as nat));
        assert(Exp_int(x * x, y / 2) == (x * x) * Exp_int(x * x, (y / 2 - 1) as nat));
        lemma_exp_properties(x * x, y / 2);
    }
}

proof fn lemma_exp_odd(x: nat, y: nat)
    requires
        y > 0,
        y % 2 == 1,
    ensures
        Exp_int(x, y) == x * Exp_int(x * x, y / 2),
    decreases y,
{
    if y == 1 {
        assert(Exp_int(x, 1) == x);
        assert(Exp_int(x * x, 0) == 1);
    } else {
        lemma_exp_properties(x, y);
        lemma_exp_even(x, (y - 1) as nat);
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
        assert((y - 1) / 2 == y / 2);
    }
}

exec fn int_to_bitstring(n: u64) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == n,
    decreases n,
{
    let mut result = Vec::new();
    let mut num = n;
    
    if num == 0 {
        result.push('0');
        return result;
    }
    
    while num > 0
        invariant
            ValidBitString(result@),
            Str2Int(result@) + num * Exp_int(2, result@.len() as nat) == n,
        decreases num,
    {
        if num % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        num = num / 2;
    }
    
    result
}

/* helper modified by LLM (iteration 2): fixed type mismatch in ensures clause */
exec fn modular_multiply(a: u64, b: u64, m: u64) -> (res: u64)
    requires
        m > 0,
        a < m,
        b < m,
    ensures
        res == ((a as int) * (b as int)) % (m as int),
        res < m,
{
    ((a % m) * (b % m)) % m
}

/* helper modified by LLM (iteration 2): fixed type mismatches in invariant */
exec fn modular_exp_u64(base: u64, exp: u64, modulus: u64) -> (res: u64)
    requires
        modulus > 1,
        base < modulus,
    ensures
        res == Exp_int(base as nat, exp as nat) % (modulus as nat),
        res < modulus,
    decreases exp,
{
    if exp == 0 {
        return 1;
    }
    
    let mut result: u64 = 1;
    let mut b = base % modulus;
    let mut e = exp;
    
    while e > 0
        invariant
            result < modulus,
            b < modulus,
            ((result as int) * Exp_int(b as nat, e as nat)) % (modulus as int) == Exp_int(base as nat, exp as nat) % (modulus as int),
        decreases e,
    {
        if e % 2 == 1 {
            proof { lemma_exp_odd(b as nat, e as nat); }
            result = modular_multiply(result, b, modulus);
        }
        if e > 1 {
            proof { 
                if e % 2 == 0 {
                    lemma_exp_even(b as nat, e as nat);
                } else {
                    lemma_exp_odd(b as nat, e as nat);
                }
            }
            b = modular_multiply(b, b, modulus);
        }
        e = e / 2;
    }
    
    result
}

exec fn bitstring_to_u64(s: &[char]) -> (res: u64)
    requires
        ValidBitString(s@),
        s@.len() <= 64,
        Str2Int(s@) < u64::MAX,
    ensures
        res == Str2Int(s@),
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            result == Str2Int(s@.subrange(0, i as int)),
        decreases s.len() - i,
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
exec fn ModExp_ModExpPow2_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed type comparison with nat */
    if sy@.len() == 0nat {
        panic!("Exponent string cannot be empty");
    }
    
    let x_val = bitstring_to_u64(sx);
    let y_val = bitstring_to_u64(sy);
    let z_val = bitstring_to_u64(sz);
    
    let result_val = modular_exp_u64(x_val, y_val, z_val);
    
    int_to_bitstring(result_val)
}
// </vc-code>

fn main() {}
}
