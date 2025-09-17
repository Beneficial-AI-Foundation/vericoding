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
proof fn exp_base_case_lemma(x: nat) 
    ensures Exp_int(x, 0) == 1 
{
}

proof fn exp_recursive_lemma(x: nat, y: nat)
    requires y > 0
    ensures Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat)
{
}

proof fn str2int_base_case_lemma()
    ensures Str2Int(Seq::empty()) == 0
{
}

proof fn str2int_recursive_lemma(s: Seq<char>)
    requires ValidBitString(s), s.len() > 0
    ensures Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
{
}

proof fn str2int_nonnegative_lemma(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) >= 0
{
}

proof fn mod_exp_power2_zeroes_lemma(base: nat, exp: nat, modulus: nat)
    requires modulus > 1
    ensures Exp_int(base, exp) % modulus == Exp_int(base % modulus, exp) % modulus
{
}

proof fn nat_arithmetic_ops_lemma(a: nat, b: nat)
    requires b > 0
    ensures 
        a % b >= 0,
        a / b >= 0,
        a % b < b,
        a == (a / b) * b + (a % b)
{
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed type mismatches and arithmetic operations */
    let mut result = Vec::new();
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    
    proof {
        mod_exp_power2_zeroes_lemma(x_val, y_val, z_val);
        exp_base_case_lemma(x_val);
        exp_recursive_lemma(x_val, y_val);
        str2int_base_case_lemma();
        str2int_recursive_lemma(sy@);
        str2int_nonnegative_lemma(sy@);
        nat_arithmetic_ops_lemma(y_val, 2);
    }
    
    let mut base_mod: nat = x_val % z_val;
    let mut exponent: nat = y_val;
    let mut res: nat = 1;
    
    while exponent > 0
        invariant
            exponent <= y_val,
            res * Exp_int(base_mod, exponent) % z_val == Exp_int(x_val, y_val) % z_val,
            res < z_val,
            base_mod < z_val,
        decreases exponent
    {
        if exponent % 2 == 1 {
            res = (res * base_mod) % z_val;
        }
        base_mod = (base_mod * base_mod) % z_val;
        exponent = exponent / 2;
    }
    
    // Convert result to binary string
    let mut temp: nat = res;
    while temp > 0
        invariant temp >= 0, temp <= res
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
    if result.is_empty() {
        result.push('0');
    }
    
    result
}
// </vc-code>

fn main() {}
}
