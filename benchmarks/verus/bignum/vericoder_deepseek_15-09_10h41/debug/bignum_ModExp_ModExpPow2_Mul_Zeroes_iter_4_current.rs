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
/* helper modified by LLM (iteration 4): Fixed type annotations and added proper nat/int conversion helpers */
proof fn helper_lemma_exp_mod(x: nat, y: nat, m: nat) 
    requires m > 1
    ensures Exp_int(x, y) % m == (if y == 0 { 1nat % m } else { (x % m) * Exp_int(x, (y - 1) as nat) % m }) % m
{
    if y == 0 {
        assert(Exp_int(x, y) % m == 1nat % m);
    } else {
        helper_lemma_exp_mod(x, (y - 1) as nat, m);
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
        assert(Exp_int(x, y) % m == (x * Exp_int(x, (y - 1) as nat)) % m);
        assert((x * Exp_int(x, (y - 1) as nat)) % m == ((x % m) * (Exp_int(x, (y - 1) as nat) % m)) % m);
    }
}
spec fn int_to_nat(x: int) -> nat
    requires x >= 0
{
    x as nat
}
fn nat_to_int(n: nat) -> int {
    n as int
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fixed variable declarations and type handling */
{
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    let mut result_val = 1;
    
    proof {
        helper_lemma_exp_mod(x_val, y_val, z_val);
    }
    
    let mut current_exp: int = nat_to_int(y_val);
    while current_exp > 0
        invariant
            result_val == Exp_int(x_val, int_to_nat(y_val - current_exp)) % z_val,
            current_exp <= nat_to_int(y_val),
            current_exp >= 0
        decreases current_exp
    {
        result_val = (result_val * nat_to_int(x_val)) % nat_to_int(z_val);
        current_exp = current_exp - 1;
    }
    
    let mut result_vec = Vec::new();
    if result_val == 0 {
        result_vec.push('0');
    } else {
        let mut temp_val = result_val;
        while temp_val > 0
            invariant
                temp_val >= 0
            decreases temp_val
        {
            if temp_val % 2 == 0 {
                result_vec.push('0');
            } else {
                result_vec.push('1');
            }
            temp_val = temp_val / 2;
        }
        result_vec.reverse();
    }
    result_vec
}
// </vc-code>

fn main() {}
}
