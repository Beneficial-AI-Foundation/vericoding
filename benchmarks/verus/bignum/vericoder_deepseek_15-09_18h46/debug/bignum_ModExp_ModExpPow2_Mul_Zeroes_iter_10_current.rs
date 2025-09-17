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
/* helper modified by LLM (iteration 10): Fix zero_bitstring function signature and implementation */
fn zero_bitstring(length: usize) -> (res: Vec<char>)
    ensures ValidBitString(res@), res@.len() == length as nat, forall |i: int| 0 <= i && i < res@.len() as int ==> res@[i] == '0'
{
    let mut res = Vec::with_capacity(length);
    let mut i: usize = 0;
    while i < length
        invariant
            i <= length,
            res@.len() == i as nat,
            forall |j: int| 0 <= j && j < i as int ==> res@[j] == '0'
        decreases length - i
    {
        res.push('0');
        i += 1;
    }
    res
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fix result variable usage in ensures clause */
{
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    
    if x_val % z_val == 0 {
        let result = zero_bitstring(1);
        return result;
    }
    
    mod_exp_property(x_val, y_val, z_val);
    assert(Exp_int(x_val, y_val) % z_val == Exp_int(x_val % z_val, y_val) % z_val);
    
    let base_initial = x_val % z_val;
    let mut result_val: nat = 1;
    let mut exp_remaining = y_val;
    let mut current_base = base_initial;
    
    while exp_remaining > 0
        invariant
            exp_remaining <= y_val,
            current_base == Exp_int(base_initial, 1 << (y_val - exp_remaining)) % z_val,
            result_val * Exp_int(current_base, exp_remaining) % z_val == Exp_int(base_initial, y_val) % z_val
        decreases exp_remaining
    {
        if exp_remaining % 2 == 1 {
            result_val = (result_val * current_base) % z_val;
        }
        current_base = (current_base * current_base) % z_val;
        exp_remaining = exp_remaining / 2;
    }
    
    let mut res_digits: Vec<char> = Vec::new();
    let mut temp = result_val;
    while temp > 0
        invariant ValidBitString(res_digits@)
        decreases temp
    {
        if temp % 2 == 1 {
            res_digits.push('1');
        } else {
            res_digits.push('0');
        }
        temp = temp / 2;
    }
    
    if res_digits.is_empty() {
        res_digits.push('0');
    }
    
    res_digits.reverse();
    res_digits
}
// </vc-code>

fn main() {}
}
