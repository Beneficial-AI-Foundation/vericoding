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
/* helper modified by LLM (iteration 8): Fix ModExp proof with proper recursive calls and assertions */
proof fn mod_exp_property(x: nat, e: nat, m: nat) 
    requires m > 1
    ensures Exp_int(x, e) % m == (if x % m == 0 then 0 else Exp_int(x % m, e) % m)
{
    if e == 0 {
        assert(Exp_int(x, 0) == 1);
        assert(1 % m == 1);
        if x % m == 0 {
            assert(0 == 0);
        } else {
            assert(Exp_int(x % m, 0) == 1);
            assert(1 % m == 1);
        }
    } else {
        mod_exp_property(x, e - 1, m);
        if x % m == 0 {
            assert(Exp_int(x, e) == x * Exp_int(x, e - 1));
            assert(x % m == 0);
            assert((x * Exp_int(x, e - 1)) % m == 0);
        } else {
            let x_mod = x % m;
            mod_exp_property(x_mod, e - 1, m);
            assert(Exp_int(x, e) == x * Exp_int(x, e - 1));
            assert(Exp_int(x, e) % m == (x * Exp_int(x, e - 1)) % m);
            assert((x * Exp_int(x, e - 1)) % m == (x_mod * Exp_int(x, e - 1)) % m);
            assert(Exp_int(x_mod, e) == x_mod * Exp_int(x_mod, e - 1));
            assert((x_mod * Exp_int(x, e - 1)) % m == (x_mod * Exp_int(x_mod, e - 1)) % m);
        }
    }
}

fn zero_bitstring(length: usize) -> Vec<char> 
    ensures ValidBitString(result@), result@.len() == length as nat, forall |i: int| 0 <= i && i < result@.len() as int ==> result@[i] == '0'
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
{
    /* code modified by LLM (iteration 8): Fix modular exponentiation loop invariants and verification */
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    
    if x_val % z_val == 0 {
        return zero_bitstring(1);
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
