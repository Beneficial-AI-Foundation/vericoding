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

// Helper lemma: relationship between Str2Int and removing last bit
proof fn lemma_str2int_pop(s: Seq<char>)
requires s.len() > 0, ValidBitString(s)
ensures Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.last() == '1' { 1nat } else { 0nat })
{
    assert(s.index(s.len() as int - 1) == s.last());
}

// Helper lemma for exponentiation with even exponent
proof fn lemma_exp_even(x: nat, y: nat)
requires y > 0, y % 2 == 0
ensures Exp_int(x, y) == Exp_int(x * x, y / 2)
decreases y
{
    if y == 2 {
        assert(Exp_int(x, 2) == x * x * 1);
        assert(Exp_int(x * x, 1) == x * x * 1);
    } else {
        assert(y >= 2);
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
        assert(Exp_int(x, (y - 1) as nat) == x * Exp_int(x, (y - 2) as nat));
        lemma_exp_even(x, (y - 2) as nat);
        assert(Exp_int(x, (y - 2) as nat) == Exp_int(x * x, ((y - 2) / 2) as nat));
        assert((y - 2) / 2 == y / 2 - 1);
    }
}

// Helper lemma for exponentiation with odd exponent
proof fn lemma_exp_odd(x: nat, y: nat)
requires y > 0, y % 2 == 1
ensures Exp_int(x, y) == x * Exp_int(x * x, y / 2)
decreases y
{
    if y == 1 {
        assert(Exp_int(x, 1) == x * 1);
        assert(Exp_int(x * x, 0) == 1);
    } else {
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
        lemma_exp_even(x, (y - 1) as nat);
        assert(Exp_int(x, (y - 1) as nat) == Exp_int(x * x, ((y - 1) / 2) as nat));
        assert((y - 1) / 2 == y / 2);
    }
}

// Convert binary string to nat
exec fn binary_to_nat(s: &[char]) -> (res: u64)
requires ValidBitString(s@)
ensures res == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
    invariant
        0 <= i <= s.len(),
        ValidBitString(s@),
        result == Str2Int(s@.subrange(0, i as int))
    {
        let bit = if s[i] == '1' { 1u64 } else { 0u64 };
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
    let mut result = Vec::<char>::new();
    let mut num = n;
    
    if num == 0 {
        return result;
    }
    
    while num > 0
    invariant 
        ValidBitString(result@),
        Str2Int(result@) + num * Exp_int(2, result@.len() as nat) == n,
        num >= 0
    {
        let bit = if num % 2 == 0 { '0' } else { '1' };
        result.push(bit);
        num = num / 2;
    }
    
    result
}

// Helper to compute (a * b) % m
exec fn mul_mod(a: u64, b: u64, m: u64) -> (res: u64)
requires m > 0
ensures res == (a as nat * b as nat) % (m as nat)
{
    ((a as u128 * b as u128) % m as u128) as u64
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
    
    while exp > 0
    invariant
        z_val > 1,
        z_val == Str2Int(sz@),
        result < z_val,
        base < z_val,
        (result as nat * Exp_int(base as nat, exp as nat)) % (z_val as nat) == Exp_int(x_val as nat, y_val as nat) % (z_val as nat)
    {
        if exp % 2 == 1 {
            proof {
                lemma_exp_odd(base as nat, exp as nat);
            }
            result = mul_mod(result, base, z_val);
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
        assert((result as nat) % (z_val as nat)
// </vc-code>

fn main() {}
}