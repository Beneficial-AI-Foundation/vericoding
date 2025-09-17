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
/* helper modified by LLM (iteration 7): fixed reverse call by using temporary variable */
exec fn char_to_usize(c: char) -> (result: usize)
    requires c == '0' || c == '1'
    ensures c == '0' ==> result == 0,
            c == '1' ==> result == 1
{
    if c == '1' { 1 } else { 0 }
}

exec fn usize_to_char(n: usize) -> (result: char)
    requires n == 0 || n == 1
    ensures n == 0 ==> result == '0',
            n == 1 ==> result == '1'
{
    if n == 1 { '1' } else { '0' }
}

exec fn str_slice_to_usize(s: &[char]) -> (result: usize)
    requires ValidBitString(s@)
{
    let mut result: usize = 0;
    let mut i = 0;
    while i < s.len()
        invariant 0 <= i <= s.len()
    {
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        i = i + 1;
    }
    result
}

exec fn usize_to_bit_string(n: usize) -> (result: Vec<char>)
    ensures ValidBitString(result@)
{
    if n == 0 {
        vec!['0']
    } else {
        let mut result = Vec::new();
        let mut temp = n;
        while temp > 0
            invariant ValidBitString(result@)
        {
            if temp % 2 == 1 {
                result.push('1');
            } else {
                result.push('0');
            }
            temp = temp / 2;
        }
        let mut result_to_reverse = result;
        result_to_reverse.reverse();
        result_to_reverse
    }
}

exec fn modular_exp_usize(base: usize, exp: usize, modulus: usize) -> (result: usize)
    requires modulus > 1
    decreases exp
{
    if exp == 0 {
        1 % modulus
    } else {
        let half_exp = exp / 2;
        let half_result = modular_exp_usize(base, half_exp, modulus);
        let squared = (half_result * half_result) % modulus;
        if exp % 2 == 1 {
            (squared * (base % modulus)) % modulus
        } else {
            squared
        }
    }
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
    /* code modified by LLM (iteration 7): unchanged body implementation */
    let base_usize = str_slice_to_usize(sx);
    let exp_usize = str_slice_to_usize(sy);
    let mod_usize = str_slice_to_usize(sz);
    
    let result_usize = modular_exp_usize(base_usize, exp_usize, mod_usize);
    let result_vec = usize_to_bit_string(result_usize);
    
    result_vec
}
// </vc-code>

fn main() {}
}
