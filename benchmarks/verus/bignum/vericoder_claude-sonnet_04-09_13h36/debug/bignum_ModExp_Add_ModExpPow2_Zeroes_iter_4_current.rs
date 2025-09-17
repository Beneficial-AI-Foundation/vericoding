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
proof fn lemma_str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{
}

proof fn lemma_str2int_single_zero()
    ensures Str2Int(seq!['0']) == 0
{
}

proof fn lemma_str2int_single_one()
    ensures Str2Int(seq!['1']) == 1
{
}

proof fn lemma_exp_zero()
    ensures forall |x: nat| Exp_int(x, 0) == 1
{
}

proof fn lemma_exp_one()
    ensures forall |x: nat| Exp_int(x, 1) == x
{
}

proof fn lemma_mod_exp_zero(m: nat)
    requires m > 1
    ensures forall |x: nat| Exp_int(x, 0) % m == 1 % m
{
}

proof fn char_to_nat(c: char) -> (result: nat)
    requires c == '0' || c == '1'
    ensures result == (if c == '1' { 1nat } else { 0nat })
{
    if c == '1' { 1nat } else { 0nat }
}

exec fn nat_to_char(n: nat) -> (result: char)
    requires n == 0 || n == 1
    ensures result == (if n == 1 { '1' } else { '0' })
{
    if n == 1 { '1' } else { '0' }
}

exec fn int_to_bit_string(mut n: nat) -> (result: Vec<char>)
    ensures ValidBitString(result@)
{
    let mut result = Vec::new();
    if n == 0 {
        result.push('0');
        return result;
    }
    
    while n > 0
        invariant ValidBitString(result@)
    {
        if n % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        n = n / 2;
    }
    
    result.reverse();
    result
}

proof fn lemma_exp_identity()
    ensures forall |base: nat, exp: nat| Exp_int(base, exp) == Exp_int(base, exp)
{
}

proof fn lemma_mod_invariant(result_val: nat, base: nat, exp: nat, modulus: nat, original_base: nat, original_exp: nat)
    requires modulus > 1
    requires result_val * Exp_int(base, exp) % modulus == Exp_int(original_base, original_exp) % modulus
    ensures result_val * Exp_int(base, exp) % modulus == Exp_int(original_base, original_exp) % modulus
{
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    if sy.len() == 0 {
        return int_to_bit_string(1);
    }
    
    if Str2Int(sy@) == 0 {
        proof {
            lemma_exp_zero();
            lemma_mod_exp_zero(Str2Int(sz@));
        }
        return int_to_bit_string(1 % Str2Int(sz@));
    }
    
    if Str2Int(sy@) == 1 {
        proof {
            lemma_exp_one();
        }
        return int_to_bit_string(Str2Int(sx@) % Str2Int(sz@));
    }
    
    // For the general case, we'll use a simple iterative approach
    let mut base = Str2Int(sx@);
    let mut exp = Str2Int(sy@);
    let modulus = Str2Int(sz@);
    let mut result_val = 1nat;
    
    while exp > 0
        invariant modulus > 1,
        invariant result_val * Exp_int(base, exp) % modulus == Exp_int(Str2Int(sx@), Str2Int(sy@)) % modulus,
    {
        if exp % 2 == 1 {
            result_val = (result_val * base) % modulus;
        }
        base = (base * base) % modulus;
        exp = exp / 2;
    }
    
    int_to_bit_string(result_val)
}
// </vc-code>

fn main() {}
}