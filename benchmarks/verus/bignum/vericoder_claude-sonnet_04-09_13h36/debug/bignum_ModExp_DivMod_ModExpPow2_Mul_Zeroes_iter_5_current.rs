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

proof fn lemma_exp_int_zero()
    ensures forall |x: nat| Exp_int(x, 0) == 1
{
}

proof fn lemma_exp_int_one()
    ensures forall |x: nat| Exp_int(x, 1) == x
{
}

proof fn lemma_mod_properties()
    ensures forall |a: nat, b: nat, m: nat| m > 0 ==> (a * b) % m == ((a % m) * (b % m)) % m
{
}

exec fn int_to_bitstring(mut n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@)
{
    if n == 0 {
        return vec!['0'];
    }
    
    let mut result = Vec::<char>::new();
    while n > 0
        invariant ValidBitString(result@)
    {
        if n % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        n = n / 2;
    }
    
    result.reverse();
    result
}

exec fn bitstring_to_int(s: &[char]) -> (res: nat)
    requires ValidBitString(s@)
    ensures res == Str2Int(s@)
{
    if s.len() == 0 {
        return 0;
    }
    
    let mut result: nat = 0;
    let mut i = 0;
    
    while i < s.len()
        invariant 0 <= i <= s.len(),
                 ValidBitString(s@)
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
exec fn ModExp_DivMod_ModExpPow2_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    if sy.len() == 0 {
        return vec!['1'];
    }
    
    let x = bitstring_to_int(sx);
    let y = bitstring_to_int(sy);
    let z = bitstring_to_int(sz);
    
    if y == 0 {
        proof {
            lemma_exp_int_zero();
        }
        return vec!['1'];
    }
    
    if x == 0 {
        return vec!['0'];
    }
    
    if x == 1 {
        return vec!['1'];
    }
    
    let mut result: nat = 1;
    let mut base = x % z;
    let mut exp = y;
    
    while exp > 0
        invariant z > 1,
                 result < z,
                 base < z
    {
        if exp % 2 == 1 {
            result = (result * base) % z;
        }
        base = (base * base) % z;
        exp = exp / 2;
    }
    
    int_to_bitstring(result)
}
// </vc-code>

fn main() {}
}