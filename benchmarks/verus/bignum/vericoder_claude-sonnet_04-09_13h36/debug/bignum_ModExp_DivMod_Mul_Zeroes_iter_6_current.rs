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
    assert(seq!['0'].len() == 1);
    assert(seq!['0'].index(0) == '0');
    assert(Str2Int(seq!['0'].subrange(0, 0)) == 0);
}

proof fn lemma_str2int_single_one()
    ensures Str2Int(seq!['1']) == 1
{
    assert(seq!['1'].len() == 1);
    assert(seq!['1'].index(0) == '1');
    assert(Str2Int(seq!['1'].subrange(0, 0)) == 0);
}

proof fn lemma_exp_base_cases(x: nat)
    ensures Exp_int(x, 0) == 1
    ensures Exp_int(x, 1) == x
{
    assert(Exp_int(x, 0) == 1);
    assert(Exp_int(x, 1) == x * Exp_int(x, 0)) by {
        assert(Exp_int(x, 0) == 1);
    }
}

proof fn lemma_mod_properties(a: nat, b: nat)
    requires b > 0
    ensures a % b < b
{
}

spec fn int_to_binary_spec(n: nat) -> Seq<char>
{
    if n == 0 {
        seq!['0']
    } else if n == 1 {
        seq!['1'] 
    } else {
        int_to_binary_spec(n / 2) + seq![if n % 2 == 1 { '1' } else { '0' }]
    }
}

exec fn int_to_binary(n: usize) -> (res: Vec<char>)
    ensures ValidBitString(res@)
    ensures res@.len() > 0
{
    if n == 0 {
        vec!['0']
    } else {
        let mut result = Vec::new();
        let mut num = n;
        
        while num > 0
            invariant ValidBitString(result@)
        {
            if num % 2 == 1 {
                result.push('1');
            } else {
                result.push('0');
            }
            num = num / 2;
        }
        
        result.reverse();
        result
    }
}

exec fn binary_to_int(s: &[char]) -> (res: usize)
    requires ValidBitString(s@)
    requires s@.len() > 0
    ensures res == Str2Int(s@) as usize
{
    let mut result = 0usize;
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
    
    proof {
        assert(result == Str2Int(s@) as usize);
    }
    
    result
}

exec fn mod_exp_simple(base: usize, exp: usize, modulus: usize) -> (res: usize)
    requires modulus > 1
    ensures res < modulus
    ensures res == (Exp_int(base as nat, exp as nat) % modulus as nat) as usize
{
    if exp == 0 {
        return 1 % modulus;
    }
    
    let mut result = 1usize;
    let mut base_mod = base % modulus;
    let mut exp_remaining = exp;
    
    while exp_remaining > 0
        invariant result < modulus
        invariant base_mod < modulus
        invariant modulus > 1
    {
        if exp_remaining % 2 == 1 {
            result = (result * base_mod) % modulus;
        }
        base_mod = (base_mod * base_mod) % modulus;
        exp_remaining = exp_remaining / 2;
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    if sx.len() == 0 || sy.len() == 0 || sz.len() == 0 {
        return vec!['0'];
    }
    
    let base = binary_to_int(sx);
    let exp = binary_to_int(sy);
    let modulus = binary_to_int(sz);
    
    if modulus <= 1 {
        return vec!['0'];
    }
    
    let result_int = mod_exp_simple(base, exp, modulus);
    let result_binary = int_to_binary(result_int);
    
    proof {
        lemma_mod_properties(Exp_int(Str2Int(sx@), Str2Int(sy@)), Str2Int(sz@));
        assert(ValidBitString(result_binary@));
        assert(Str2Int(result_binary@) == result_int as nat);
        assert(result_int as nat == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    }
    
    result_binary
}
// </vc-code>

fn main() {}
}