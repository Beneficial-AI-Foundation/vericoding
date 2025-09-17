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
/* helper modified by LLM (iteration 5): Fixed Exp_int spec function syntax */
spec fn Exp_int(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

proof fn nat_div_lemma(a: nat, b: nat)
    requires b > 0
    ensures a / b is nat
{
}

proof fn nat_mod_lemma(a: nat, b: nat)
    requires b > 0
    ensures a % b is nat
{
}

proof fn nat_sub_lemma(a: nat, b: nat)
    requires a >= b
    ensures (a - b) is nat
{
}

proof fn nat_convert_lemma(n: nat)
    ensures n as int == n
{
}

proof fn exp_int_spec_lemma(x: nat, y: nat)
    decreases y
    ensures Exp_int(x, y) >= 0
{
    if y > 0 {
        exp_int_spec_lemma(x, (y - 1) as nat);
    }
}

proof fn arithmetic_ops_preserve_nat(a: nat, b: nat)
    requires b > 0
    ensures (a + b) is nat, (a * b) is nat, (a % b) is nat, (a / b) is nat
{
}

proof fn mod_exp_power2_zeroes_lemma(x: nat, y: nat, z: nat)
    requires z > 1
    ensures Exp_int(x, y) % z is nat
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
/* code modified by LLM (iteration 5): Fixed compilation error in Exp_int spec */
{
    let mut result = Vec::new();
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    
    proof {
        nat_convert_lemma(x_val);
        nat_convert_lemma(y_val);
        nat_convert_lemma(z_val);
        nat_div_lemma(y_val, 2);
        nat_mod_lemma(y_val, 2);
        exp_int_spec_lemma(x_val, y_val);
        mod_exp_power2_zeroes_lemma(x_val, y_val, z_val);
    }
    
    let mut base_mod: nat = x_val % z_val;
    let mut exponent: nat = y_val;
    let mut res: nat = 1;
    
    while exponent > 0 as nat
        invariant
            exponent <= y_val,
            res * Exp_int(base_mod, exponent) % z_val == Exp_int(x_val, y_val) % z_val,
            res < z_val,
            base_mod < z_val,
            exponent is nat
        decreases exponent
    {
        proof {
            nat_convert_lemma(exponent);
            nat_mod_lemma(exponent, 2);
            nat_div_lemma(exponent, 2);
        }
        
        if exponent % (2 as nat) == (1 as nat) {
            res = (res * base_mod) % z_val;
        }
        base_mod = (base_mod * base_mod) % z_val;
        exponent = exponent / (2 as nat);
    }
    
    let mut temp: nat = res;
    while temp > 0 as nat
        invariant temp >= 0, temp <= res, temp is nat
        decreases temp
    {
        proof {
            nat_convert_lemma(temp);
            nat_mod_lemma(temp, 2);
            nat_div_lemma(temp, 2);
        }
        
        if temp % (2 as nat) == (1 as nat) {
            result.push('1');
        } else {
            result.push('0');
        }
        temp = temp / (2 as nat);
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
