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
proof fn exp_int_monotonic(x: nat, y1: nat, y2: nat) requires y1 <= y2, x >= 1 ensures Exp_int(x, y1) <= Exp_int(x, y2) { if y1 < y2 { let y2_minus_1: nat = (y2 - 1) as nat; exp_int_monotonic(x, y1, y2_minus_1); } } proof fn str2int_nonnegative(s: Seq<char>) requires ValidBitString(s) ensures Str2Int(s) >= 0 { } proof fn str2int_monotonic(s1: Seq<char>, s2: Seq<char>) requires ValidBitString(s1), ValidBitString(s2), s1.len() <= s2.len() ensures Str2Int(s1) <= Str2Int(s2) { } proof fn exp_int_property(x: nat, y: nat) requires x >= 1 ensures Exp_int(x, y) >= 1 { } proof fn mod_exp_lemma(a: nat, b: nat, m: nat) requires m > 1, b >= 1 ensures Exp_int(a, b) % m == (a * Exp_int(a, (b - 1) as nat)) % m { }
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fix type mismatches with nat/int conversions */
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    let mut result: nat = 1nat;
    let mut base: nat = (x_val % z_val) as nat;
    let mut exp: nat = y_val;
    
    proof {
        str2int_nonnegative(sx@);
        str2int_nonnegative(sy@);
        str2int_nonnegative(sz@);
        exp_int_property(x_val, y_val);
    }
    
    while exp > 0nat
        invariant
            result >= 0, result < z_val,
            Exp_int(x_val, y_val) % z_val == (result * Exp_int(base, exp)) % z_val,
            base == Exp_int(x_val % z_val, 1nat) % z_val
        decreases exp
    {
        if exp % 2nat == 1nat {
            result = (result * base) % z_val;
        }
        base = (base * base) % z_val;
        let exp_div_2: nat = (exp / 2nat) as nat;
        exp = exp_div_2;
        
        proof {
            let b_minus_1: nat = (y_val - 1) as nat;
            mod_exp_lemma(x_val, y_val, z_val);
        }
    }
    
    let mut res_vec = Vec::new();
    let mut temp: nat = result;
    
    while temp > 0nat
        invariant
            temp >= 0,
            ValidBitString(res_vec@),
            Str2Int(res_vec@) == result - temp * Exp_int(2nat, res_vec@.len() as nat)
        decreases temp
    {
        if temp % 2nat == 1nat {
            res_vec.push('1');
        } else {
            res_vec.push('0');
        }
        let temp_div_2: nat = (temp / 2nat) as nat;
        temp = temp_div_2;
    }
    
    if res_vec.is_empty() {
        res_vec.push('0');
    }
    
    res_vec.reverse();
    res_vec
}
// </vc-code>

fn main() {}
}
