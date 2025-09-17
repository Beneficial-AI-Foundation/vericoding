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
spec fn mod_exp_helper(base: nat, exp: nat, modulus: nat) -> nat
    recommends modulus > 1
    decreases exp
{
    if exp == 0 {
        1nat % modulus
    } else {
        let half = mod_exp_helper(base, exp / 2, modulus);
        let half_squared = (half * half) % modulus;
        if exp % 2 == 0 {
            half_squared
        } else {
            (half_squared * base) % modulus
        }
    }
}

proof fn mod_exp_helper_correct(base: nat, exp: nat, modulus: nat)
    requires modulus > 1
    ensures mod_exp_helper(base, exp, modulus) == Exp_int(base, exp) % modulus
    decreases exp
{
    if exp == 0 {
    } else {
        mod_exp_helper_correct(base, exp / 2, modulus);
        assert(Exp_int(base, exp) == if exp % 2 == 0 { Exp_int(base, exp / 2) * Exp_int(base, exp / 2) } else { Exp_int(base, exp / 2) * Exp_int(base, exp / 2) * base });
    }
}

/* helper modified by LLM (iteration 3): fixed nat literal syntax */
exec fn int_to_bitstring(n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@),
            Str2Int(res@) == n
{
    let mut result = Vec::<char>::new();
    let mut num = n;
    
    if num == 0 {
        result.push('0');
        return result;
    }
    
    while num > 0
        invariant
            ValidBitString(result@),
            Str2Int(result@) + num * Exp_int(2, result@.len() as nat) == n
    {
        if num % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        num = num / 2;
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): compute modular exponentiation */
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    
    proof {
        mod_exp_helper_correct(x_val, y_val, z_val);
    }
    
    let result_val = mod_exp_helper(x_val, y_val, z_val);
    let result = int_to_bitstring(result_val);
    
    result
}
// </vc-code>

fn main() {}
}
