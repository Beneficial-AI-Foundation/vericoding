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
spec fn pow_mod_helper(base: nat, exp: nat, modulus: nat) -> nat
    requires modulus > 0
    decreases exp
{
    if exp == 0 {
        1 % modulus
    } else if exp % 2 == 0 {
        let half = pow_mod_helper(base, exp / 2, modulus);
        (half * half) % modulus
    } else {
        (base * pow_mod_helper(base, exp - 1, modulus)) % modulus
    }
}

spec fn char_to_digit(c: char) -> nat
{
    if c == '1' { 1 } else { 0 }
}

proof fn str2int_bounds(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) < Exp_int(2, s.len())
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        str2int_bounds(s.subrange(0, s.len() as int - 1));
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    if sy.len() == 1 && sy[0] == '0' {
        let mut result = Vec::new();
        result.push('1');
        return result;
    }
    
    let base_val = Str2Int(sx@);
    let exp_val = Str2Int(sy@);
    let mod_val = Str2Int(sz@);
    
    let mut result_val = 1;
    let mut base_curr = base_val % mod_val;
    let mut exp_curr = exp_val;
    
    while exp_curr > 0
        invariant
            mod_val > 1,
            result_val < mod_val,
            base_curr < mod_val,
            (result_val * Exp_int(base_curr, exp_curr)) % mod_val == Exp_int(base_val, exp_val) % mod_val
        decreases exp_curr
    {
        if exp_curr % 2 == 1 {
            result_val = (result_val * base_curr) % mod_val;
        }
        base_curr = (base_curr * base_curr) % mod_val;
        exp_curr = exp_curr / 2;
    }
    
    let mut result = Vec::new();
    if result_val == 0 {
        result.push('0');
    } else {
        let mut temp = result_val;
        while temp > 0
            invariant temp >= 0
            decreases temp
        {
            if temp % 2 == 1 {
                result.push('1');
            } else {
                result.push('0');
            }
            temp = temp / 2;
        }
        result.reverse();
    }
    
    result
}
// </vc-code>

fn main() {}
}
