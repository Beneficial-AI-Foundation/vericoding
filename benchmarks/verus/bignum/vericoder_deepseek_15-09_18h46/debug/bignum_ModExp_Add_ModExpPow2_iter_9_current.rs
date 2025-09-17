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
/* helper modified by LLM (iteration 9): Fix nat type conversions and ensure proper arithmetic operations */
proof fn lemma_nat_div(a: nat, b: nat)
    requires b > 0
    ensures a / b as nat == a / b
{
}

proof fn lemma_nat_mod(a: nat, b: nat)
    requires b > 0
    ensures a % b as nat == a % b
{
}

proof fn lemma_mod_exp_property(x: nat, y: nat, z: nat)
    requires z > 1
    ensures Exp_int(x, y) % z == Exp_int(x % z, y) % z
{
}

proof fn lemma_mod_mult_property(a: nat, b: nat, c: nat)
    requires c > 0
    ensures (a * b) % c == (a % c * b % c) % c
{
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 9): Fix integer literals and arithmetic operations for nat type */
{
    let x_val = Str2Int(sx@);
    let mut y_val: nat = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    let mut result_val: nat = 1nat;
    let mut x_mod_z: nat = x_val % z_val;
    
    while y_val > 0nat
        invariant
            result_val == Exp_int(x_val, y_val) % z_val,
        decreases y_val
    {
        if y_val % 2nat == 1nat {
            result_val = (result_val * x_mod_z) % z_val;
        }
        x_mod_z = (x_mod_z * x_mod_z) % z_val;
        y_val = y_val / 2nat;
    }
    
    let mut res_vec = Vec::<char>::new();
    let mut temp: nat = result_val;
    
    while temp > 0nat
        invariant
            ValidBitString(res_vec@),
            Str2Int(res_vec@) == temp,
        decreases temp
    {
        if temp % 2nat == 1nat {
            res_vec.push('1');
        } else {
            res_vec.push('0');
        }
        temp = temp / 2nat;
    }
    
    if res_vec.is_empty() {
        res_vec.push('0');
    } else {
        res_vec.reverse();
    }
    
    res_vec
}
// </vc-code>

fn main() {}
}
