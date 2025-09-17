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
/* helper modified by LLM (iteration 8): Fixed type conversion functions to use nat parameters */
proof fn exp_int_recursive_property(x: nat, y: nat)
    requires
        y > 0,
    ensures
        Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat)
{
    if y > 1 {
        exp_int_recursive_property(x, (y - 1) as nat);
    }
}

spec fn Str2Int_nat_to_nat(n: nat) -> nat { n }

spec fn int_to_nat(i: int) -> nat
    requires i >= 0
{
    i as nat
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 8): Fixed integer literals to use proper nat values and corrected recursive call */
{
    if sy.is_empty() {
        return Vec::new();
    }
    
    let exp_val = if sy[0] == '1' { 1 } else { 0 };
    let result_val = Exp_int(Str2Int(sx@), int_to_nat(exp_val)) % Str2Int(sz@);
    let mut res_vec = Vec::new();
    if result_val == Str2Int_nat_to_nat(1nat) {
        res_vec.push('1');
    } else {
        res_vec.push('0');
    }
    if sy.len() == 1 {
        return res_vec;
    }
    
    let y_tail = &sy[1..];
    let y_last = sy[sy.len() - 1];
    
    let base_result = ModExp_ModExpPow2_Zeroes(sx, y_tail, sz);
    
    let mut result_val = Str2Int(base_result@);
    if y_last == '1' {
        result_val = (result_val * int_to_nat(2) + int_to_nat(1)) % Str2Int(sz@);
    } else {
        result_val = (result_val * int_to_nat(2)) % Str2Int(sz@);
    }
    
    let mut res_vec = Vec::new();
    if result_val > Str2Int_nat_to_nat(0nat) {
        res_vec.push('1');
    } else {
        res_vec.push('0');
    }
    res_vec
}
// </vc-code>

fn main() {}
}
