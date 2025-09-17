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
/* helper modified by LLM (iteration 4): Added missing lemma for modular exponentiation property */
proof fn lemma_mod_exp_property(base_mod: nat, exp: nat, modulus: nat)
    requires
        modulus > 1,
    ensures
        Exp_int(base_mod, exp * 2) % modulus == (Exp_int(base_mod, exp) * Exp_int(base_mod, exp)) % modulus,
        Exp_int(base_mod, exp) % modulus == Exp_int(base_mod % modulus, exp) % modulus
{
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fixed lemma call with proper arguments and result calculation */
{
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    let mut result: nat = 1nat;
    let mut current_exp: nat = y_val;
    let base_mod: nat = x_val % z_val;
    
    while current_exp > 0nat
        invariant
            result == Exp_int(base_mod, y_val - current_exp) % z_val,
            current_exp <= y_val,
        decreases current_exp
    {
        if current_exp % 2nat == 1nat {
            result = (result * base_mod) % z_val;
        }
        current_exp = current_exp / 2nat;
        if current_exp > 0nat {
            proof { lemma_mod_exp_property(base_mod, current_exp, z_val); }
        }
    }
    
    let mut res_vec = Vec::<char>::new();
    let mut temp = result;
    while temp > 0nat
        invariant
            temp >= 0nat,
        decreases temp
    {
        if temp % 2nat == 0nat {
            res_vec.push('0');
        } else {
            res_vec.push('1');
        }
        temp = temp / 2nat;
    }
    res_vec.reverse();
    if res_vec.len() == 0 {
        res_vec.push('0');
    }
    res_vec
}
// </vc-code>

fn main() {}
}
