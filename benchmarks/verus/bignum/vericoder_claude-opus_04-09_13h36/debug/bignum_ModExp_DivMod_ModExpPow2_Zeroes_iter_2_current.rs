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
spec fn Int2Str(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq!['0']
    } else {
        Int2StrHelper(n)
    }
}

spec fn Int2StrHelper(n: nat) -> Seq<char>
    recommends n > 0
    decreases n
{
    if n == 1 {
        seq!['1']
    } else {
        Int2StrHelper(n / 2).push(if n % 2 == 1 { '1' } else { '0' })
    }
}

proof fn Int2Str_ensures_valid(n: nat)
    ensures ValidBitString(Int2Str(n))
    decreases n
{
    if n == 0 {
    } else {
        Int2StrHelper_ensures_valid(n);
    }
}

proof fn Int2StrHelper_ensures_valid(n: nat)
    requires n > 0
    ensures ValidBitString(Int2StrHelper(n))
    decreases n
{
    if n == 1 {
    } else {
        Int2StrHelper_ensures_valid(n / 2);
    }
}

proof fn Str2Int_Int2Str_inverse(n: nat)
    ensures Str2Int(Int2Str(n)) == n
    decreases n
{
    if n == 0 {
    } else {
        Str2Int_Int2StrHelper_inverse(n);
    }
}

proof fn Str2Int_Int2StrHelper_inverse(n: nat)
    requires n > 0
    ensures Str2Int(Int2StrHelper(n)) == n
    decreases n
{
    if n == 1 {
        assert(Int2StrHelper(1) == seq!['1']);
        assert(Str2Int(seq!['1']) == 1);
    } else {
        Str2Int_Int2StrHelper_inverse(n / 2);
        let s = Int2StrHelper(n / 2);
        let last_bit = if n % 2 == 1 { '1' } else { '0' };
        let full = s.push(last_bit);
        assert(full == Int2StrHelper(n));
        assert(Str2Int(full) == 2 * Str2Int(s) + (if last_bit == '1' { 1 } else { 0 }));
        assert(Str2Int(s) == n / 2);
        assert(2 * (n / 2) + n % 2 == n);
    }
}

exec fn int2str_exec(n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@)
    ensures Str2Int(res@) == n as nat
{
    proof {
        Int2Str_ensures_valid(n as nat);
        Str2Int_Int2Str_inverse(n as nat);
    }
    
    if n == 0 {
        let mut v = Vec::new();
        v.push('0');
        return v;
    }
    
    let mut result = Vec::new();
    let mut m = n;
    
    while m > 0
        invariant 
            m > 0 ==> result@ == Int2StrHelper(m as nat).subrange(0, result@.len() as int),
            m == 0 ==> result@ == Int2StrHelper(n as nat),
            ValidBitString(result@)
    {
        if m == 1 {
            result.push('1');
            m = 0;
        } else {
            result.push(if m % 2 == 1 { '1' } else { '0' });
            m = m / 2;
        }
    }
    
    result
}

proof fn exp_mod_properties(base: nat, exp: nat, modulus: nat)
    requires modulus > 1
    ensures exp > 0 ==> Exp_int(base, exp) % modulus == ((base % modulus) * (Exp_int(base, (exp - 1) as nat) % modulus)) % modulus
{
    if exp > 0 {
        assert(Exp_int(base, exp) == base * Exp_int(base, (exp - 1) as nat));
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let y_val = Str2Int(sy@);
    
    if sy@.len() == 1 && sy@[0] == '0' {
        // x^0 = 1
        let mut result = Vec::new();
        result.push('1');
        proof {
            assert(ValidBitString(result@));
            assert(Str2Int(result@) == 1);
            assert(Exp_int(Str2Int(sx@), 0) == 1);
            assert(1 % Str2Int(sz@) == Str2Int(result@));
        }
        return result;
    }
    
    // For non-zero exponent, compute using modular arithmetic
    let x_val = Str2Int(sx@);
    let z_val = Str2Int(sz@);
    
    // Compute (x^y) mod z efficiently
    let base_mod = (x_val % z_val) as u64;
    let exp_nat = y_val;
    let mod_nat = z_val;
    
    // Simple iterative modular exponentiation
    let mut result_val: u64 = 1;
    let mut base: u64 = base_mod;
    let mut exp: u64 = exp_nat as u64;
    
    while exp > 0
        invariant
            mod_nat > 1,
            mod_nat == Str2Int(sz@),
            result_val < mod_nat as u64,
            base < mod_nat as u64
    {
        if exp % 2 == 1 {
            result_val = ((result_val as u128 * base as u128) % (mod_nat as u128)) as u64;
        }
        base = ((base as u128 * base as u128) % (mod_nat as u128)) as u64;
        exp = exp / 2;
    }
    
    proof {
        exp_mod_properties(x_val, y_val, z_val);
    }
    
    let result = int2str_exec(result_val);
    
    proof {
        assert(ValidBitString(result@));
        assert(Str2Int(result@) == result_val as nat);
    }
    
    result
}
// </vc-code>

fn main() {}
}