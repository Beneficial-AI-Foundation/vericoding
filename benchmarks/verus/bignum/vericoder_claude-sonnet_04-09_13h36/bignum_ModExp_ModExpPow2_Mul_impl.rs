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

proof fn lemma_str2int_halve(s: Seq<char>)
    requires ValidBitString(s), s.len() > 0
    ensures Str2Int(if s.len() == 1 { seq!['0'] } else { s.subrange(0, s.len() as int - 1) }) == Str2Int(s) / 2
{
    if s.len() == 1 {
        assert(Str2Int(seq!['0']) == 0);
    } else {
        assert(s == s.subrange(0, s.len() as int - 1).add(seq![s.index(s.len() as int - 1)]));
    }
}

proof fn lemma_exp_int_square(x: nat, y: nat)
    ensures y % 2 == 0 ==> Exp_int(x, y) == Exp_int(Exp_int(x, y / 2), 2)
{
}

proof fn lemma_exp_int_odd(x: nat, y: nat)
    ensures y % 2 == 1 && y > 0 ==> Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat)
{
}

exec fn int_to_bitstring(n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n
{
    if n == 0 {
        vec!['0']
    } else {
        let mut result = Vec::new();
        let mut num = n;
        while num > 0
            invariant ValidBitString(result@)
        {
            if num % 2 == 0 {
                result.push('0');
            } else {
                result.push('1');
            }
            num = num / 2;
        }
        result.reverse();
        result
    }
}

exec fn bitstring_mul_mod(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
    requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), Str2Int(sz@) > 1
    ensures ValidBitString(res@), Str2Int(res@) == (Str2Int(sx@) * Str2Int(sy@)) % Str2Int(sz@)
{
    let product = Str2Int(sx@) * Str2Int(sy@);
    let modulus = Str2Int(sz@);
    let result_val = product % modulus;
    int_to_bitstring(result_val)
}

exec fn is_bit_one(s: &[char], idx: usize) -> (res: bool)
    requires idx < s@.len(), ValidBitString(s@)
    ensures res == (s@[idx as int] == '1')
{
    s[idx] == '1'
}

exec fn bitstring_halve(s: &[char]) -> (res: Vec<char>)
    requires ValidBitString(s@), s@.len() > 0
    ensures ValidBitString(res@)
{
    if s.len() == 1 {
        vec!['0']
    } else {
        let mut result = Vec::new();
        let mut i: usize = 0;
        while i < s.len() - 1
            invariant i <= s.len() - 1, ValidBitString(result@)
        {
            result.push(s[i]);
            i += 1;
        }
        result
    }
}

exec fn is_zero_bitstring(s: &[char]) -> (res: bool)
    requires ValidBitString(s@)
    ensures res == (Str2Int(s@) == 0)
{
    proof {
        lemma_str2int_single_zero();
    }
    s.len() == 1 && s[0] == '0'
}

exec fn is_one_bitstring(s: &[char]) -> (res: bool)
    requires ValidBitString(s@)
    ensures res == (Str2Int(s@) == 1)
{
    proof {
        lemma_str2int_single_one();
    }
    s.len() == 1 && s[0] == '1'
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
    if sy.len() == 0 {
        return vec!['1'];
    }
    
    if is_zero_bitstring(sy) {
        lemma_exp_int_zero();
        return vec!['1'];
    }
    
    if is_one_bitstring(sy) {
        lemma_exp_int_one();
        let product = Str2Int(sx@) % Str2Int(sz@);
        return int_to_bitstring(product);
    }
    
    let last_bit = sy[sy.len() - 1];
    let sy_half = bitstring_halve(sy);
    
    lemma_str2int_halve(sy@);
    
    let half_result = ModExp_ModExpPow2_Mul(sx, &sy_half, sz);
    let squared = bitstring_mul_mod(&half_result, &half_result, sz);
    
    if last_bit == '1' {
        lemma_exp_int_odd(Str2Int(sx@), Str2Int(sy@));
        bitstring_mul_mod(&squared, sx, sz)
    } else {
        lemma_exp_int_square(Str2Int(sx@), Str2Int(sy@));
        squared
    }
}
// </vc-code>

fn main() {}
}