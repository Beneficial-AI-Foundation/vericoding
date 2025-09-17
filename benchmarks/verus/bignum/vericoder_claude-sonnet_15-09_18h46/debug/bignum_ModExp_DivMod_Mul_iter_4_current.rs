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
/* helper modified by LLM (iteration 4): Fix nat literal comparisons and operations */
exec fn bit_string_to_vec(s: &[char]) -> (res: Vec<char>)
    requires ValidBitString(s@)
    ensures ValidBitString(res@),
            res@ == s@
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            ValidBitString(result@),
            result@ == s@.subrange(0, i as int)
    {
        result.push(s[i]);
        i += 1;
    }
    result
}

exec fn multiply_mod(a: nat, b: nat, m: nat) -> (res: nat)
    requires m > 1
    ensures res == (a * b) % m
{
    (a * b) % m
}

exec fn pow_mod_helper(base: nat, exp: nat, modulus: nat) -> (res: nat)
    requires modulus > 1
    ensures res == Exp_int(base, exp) % modulus
    decreases exp
{
    if exp == 0nat {
        1nat % modulus
    } else {
        let half_exp = exp / 2nat;
        let half_result = pow_mod_helper(base, half_exp, modulus);
        let squared = multiply_mod(half_result, half_result, modulus);
        if exp % 2nat == 1nat {
            multiply_mod(squared, base % modulus, modulus)
        } else {
            squared
        }
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fix nat literal comparisons and operations */
{
    let base = Str2Int(sx@);
    let exp = Str2Int(sy@);
    let modulus = Str2Int(sz@);
    
    let result_nat = pow_mod_helper(base, exp, modulus);
    
    let mut result = Vec::new();
    if result_nat == 0nat {
        result.push('0');
    } else {
        let mut temp = result_nat;
        let mut digits = Vec::new();
        while temp > 0nat
            invariant temp >= 0nat
        {
            if temp % 2nat == 1nat {
                digits.push('1');
            } else {
                digits.push('0');
            }
            temp = temp / 2nat;
        }
        
        let mut i = digits.len();
        while i > 0
            invariant 0 <= i <= digits.len()
        {
            i -= 1;
            result.push(digits[i]);
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}
