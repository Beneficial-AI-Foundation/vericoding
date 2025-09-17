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
proof fn helper_lemma_exp_mod(x: nat, y: nat, m: nat) 
    requires m > 1
    ensures Exp_int(x, y) % m == (if y == 0 { 1 % m } else { (x % m) * Exp_int(x, y - 1) % m }) % m
{
    if y == 0 {
        assert(Exp_int(x, y) % m == 1 % m);
    } else {
        helper_lemma_exp_mod(x, y - 1, m);
        assert(Exp_int(x, y) == x * Exp_int(x, y - 1));
        assert(Exp_int(x, y) % m == (x * Exp_int(x, y - 1)) % m);
        assert((x * Exp_int(x, y - 1)) % m == ((x % m) * (Exp_int(x, y - 1) % m)) % m);
    }
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
    let mut x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    let mut result_val = 1nat;
    let mut current_exp = y_val;
    
    proof {
        helper_lemma_exp_mod(x_val, y_val, z_val);
    }
    
    while current_exp > 0
        invariant
            result_val == Exp_int(x_val, y_val - current_exp) % z_val,
            current_exp <= y_val
        decreases current_exp
    {
        result_val = (result_val * x_val) % z_val;
        current_exp = current_exp - 1;
    }
    
    let mut result_vec = Vec::new();
    let mut temp = result_val;
    while temp > 0
        invariant
            temp >= 0
        decreases temp
    {
        if temp % 2 == 0 {
            result_vec.push('0');
        } else {
            result_vec.push('1');
        }
        temp = temp / 2;
    }
    result_vec.reverse();
    if result_vec.is_empty() {
        result_vec.push('0');
    }
    result_vec
}
// </vc-code>

fn main() {}
}
