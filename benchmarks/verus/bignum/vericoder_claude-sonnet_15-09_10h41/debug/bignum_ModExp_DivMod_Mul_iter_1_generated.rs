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
fn bit_string_to_vec(s: &[char]) -> Vec<char>
    requires ValidBitString(s@)
    ensures ValidBitString(result@),
            result@ == s@
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            ValidBitString(result@),
            result@.len() == i,
            forall |j: int| 0 <= j < i ==> result@[j] == s@[j]
    {
        result.push(s[i]);
        i += 1;
    }
    result
}

fn int_to_bit_string(mut n: nat) -> Vec<char>
    ensures ValidBitString(result@),
            Str2Int(result@) == n
{
    if n == 0 {
        let mut result = Vec::new();
        result.push('0');
        return result;
    }
    
    let mut result = Vec::new();
    let mut temp = n;
    
    while temp > 0
        invariant
            ValidBitString(result@)
        decreases temp
    {
        if temp % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        temp = temp / 2;
    }
    
    let mut reversed = Vec::new();
    let mut i = result.len();
    while i > 0
        invariant
            ValidBitString(reversed@)
    {
        i -= 1;
        reversed.push(result[i]);
    }
    
    reversed
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    if Str2Int(sy@) == 0 {
        return int_to_bit_string(1);
    }
    
    if Str2Int(sy@) == 1 {
        let base = Str2Int(sx@);
        let modulus = Str2Int(sz@);
        return int_to_bit_string(base % modulus);
    }
    
    let base = Str2Int(sx@);
    let exp_half = Str2Int(sy@) / 2;
    let modulus = Str2Int(sz@);
    
    let sy_half = int_to_bit_string(exp_half);
    let temp_result = ModExp_DivMod_Mul(&bit_string_to_vec(sx), &sy_half, sz);
    let temp_val = Str2Int(temp_result@);
    let squared = (temp_val * temp_val) % modulus;
    
    if Str2Int(sy@) % 2 == 0 {
        return int_to_bit_string(squared);
    } else {
        let final_result = (squared * base) % modulus;
        return int_to_bit_string(final_result);
    }
}
// </vc-code>

fn main() {}
}
