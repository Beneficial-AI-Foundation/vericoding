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
/* helper modified by LLM (iteration 5): Fixed type conversion helpers and added nat conversion utilities */
fn to_nat_int(x: int) -> nat
    requires x >= 0,
{
    x as nat
}

proof fn lemma_int_to_nat_equivalence(x: int)
    requires x >= 0,
    ensures x == to_nat_int(x),
{
}

proof fn lemma_div_nat(a: nat, b: nat)
    requires b > 0,
    ensures a / b >= 0,
{
}

proof fn lemma_mod_nat(a: nat, b: nat)
    requires b > 0,
    ensures a % b >= 0,
{
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type conversions between nat and int */
{
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    let mut result_val: nat = 1nat;
    let mut base = x_val % z_val;
    let mut current_y: nat = y_val;
    
    while current_y > 0nat
        invariant
            result_val < z_val,
            Exp_int(x_val, current_y) * (result_val as nat) % z_val == 0,
        decreases current_y
    {
        if current_y % 2nat == 1nat {
            result_val = (result_val * base) % z_val;
        }
        base = (base * base) % z_val;
        current_y = current_y / 2nat;
    }
    
    let mut res_vec = Vec::new();
    let mut current: nat = result_val;
    
    if current == 0nat {
        res_vec.push('0');
    } else {
        while current > 0nat
            invariant
                ValidBitString(res_vec@),
                Str2Int(res_vec@) == current,
            decreases current
        {
            if current % 2nat == 0nat {
                res_vec.push('0');
            } else {
                res_vec.push('1');
            }
            current = current / 2nat;
        }
        res_vec.reverse();
    }
    
    res_vec
}
// </vc-code>

fn main() {}
}
