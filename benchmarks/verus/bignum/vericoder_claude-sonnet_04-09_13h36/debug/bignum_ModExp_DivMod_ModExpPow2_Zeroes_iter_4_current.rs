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
{}

proof fn lemma_str2int_single_zero()
    ensures Str2Int(seq!['0']) == 0
{
    assert(seq!['0'].len() == 1);
    assert(seq!['0'].index(0) == '0');
}

proof fn lemma_str2int_single_one()
    ensures Str2Int(seq!['1']) == 1
{
    assert(seq!['1'].len() == 1);
    assert(seq!['1'].index(0) == '1');
}

proof fn lemma_valid_bit_string_empty()
    ensures ValidBitString(Seq::<char>::empty())
{}

proof fn lemma_valid_bit_string_single(c: char)
    requires c == '0' || c == '1'
    ensures ValidBitString(seq![c])
{}

exec fn int_to_bit_string(n: nat, modulus: nat) -> (res: Vec<char>)
    requires modulus > 1
    ensures ValidBitString(res@)
    ensures Str2Int(res@) == n % modulus
{
    if n == 0 {
        let mut result = Vec::new();
        result.push('0');
        proof {
            lemma_str2int_single_zero();
            lemma_valid_bit_string_single('0');
        }
        return result;
    }
    
    let mut result = Vec::new();
    let mut num = n % modulus;
    
    while num > 0
        invariant ValidBitString(result@)
        invariant num < modulus
    {
        if num % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        num = num / 2;
    }
    
    if result.len() == 0 {
        result.push('0');
    }
    
    result.reverse();
    result
}

exec fn bit_string_to_nat(s: &[char]) -> (res: nat)
    requires ValidBitString(s@)
    ensures res == Str2Int(s@)
{
    if s.len() == 0 {
        proof { lemma_str2int_empty(); }
        return 0;
    }
    
    let mut result = 0nat;
    let mut i = 0;
    
    while i < s.len()
        invariant 0 <= i <= s.len()
        invariant ValidBitString(s@)
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
exec fn ModExp_DivMod_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    if sy.len() == 0 {
        let mut result = Vec::new();
        result.push('1');
        proof {
            lemma_str2int_single_one();
            lemma_valid_bit_string_single('1');
        }
        return result;
    }
    
    let x_val = bit_string_to_nat(sx);
    let y_val = bit_string_to_nat(sy);
    let z_val = bit_string_to_nat(sz);
    
    if y_val == 0 {
        let mut result = Vec::new();
        result.push('1');
        proof {
            lemma_str2int_single_one();
            lemma_valid_bit_string_single('1');
        }
        return result;
    }
    
    let mut result = 1nat;
    let mut base = x_val % z_val;
    let mut exp = y_val;
    
    while exp > 0
        invariant base < z_val
        invariant z_val > 1
    {
        if exp % 2 == 1 {
            result = (result * base) % z_val;
        }
        base = (base * base) % z_val;
        exp = exp / 2;
    }
    
    int_to_bit_string(result, z_val)
}
// </vc-code>

fn main() {}
}