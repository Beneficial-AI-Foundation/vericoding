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
lemma lemma_str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{
}

lemma lemma_str2int_single_zero()
    ensures Str2Int(seq!['0']) == 0
{
}

lemma lemma_str2int_single_one()
    ensures Str2Int(seq!['1']) == 1
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
        let mut i = 0;
        while i < s.len() - 1
            invariant i <= s.len() - 1, ValidBitString(result@)
        {
            result.push(s[i]);
            i += 1;
        }
        result
    }
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
    
    if Str2Int(sy@) == 0 {
        return vec!['1'];
    }
    
    if Str2Int(sy@) == 1 {
        let product = Str2Int(sx@) % Str2Int(sz@);
        return int_to_bitstring(product);
    }
    
    let last_bit = sy[sy.len() - 1];
    let sy_half = bitstring_halve(sy);
    
    let half_result = ModExp_ModExpPow2_Mul(sx, &sy_half, sz);
    let squared = bitstring_mul_mod(&half_result, &half_result, sz);
    
    if last_bit == '1' {
        bitstring_mul_mod(&squared, sx, sz)
    } else {
        squared
    }
}
// </vc-code>

fn main() {}
}