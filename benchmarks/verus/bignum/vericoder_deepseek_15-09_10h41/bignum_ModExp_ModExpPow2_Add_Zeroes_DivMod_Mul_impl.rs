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
/* helper modified by LLM (iteration 5): Fixed compilation errors by using ghost blocks and proper types */
proof fn str2int_to_int(s: Seq<char>) -> (val: int)
    requires ValidBitString(s)
    ensures val == Str2Int(s) as int
{
    Str2Int(s) as int
}

fn mod_exp_helper(x: int, y: int, m: int) -> int
    requires m > 1
    ensures result == Exp_int(x as nat, y as nat) % (m as nat)
    decreases y
{
    if y == 0 {
        1
    } else if y % 2 == 1 {
        (x * mod_exp_helper((x * x) % m, y / 2, m)) % m
    } else {
        mod_exp_helper((x * x) % m, y / 2, m)
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Add_Zeroes_DivMod_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation errors by using ghost blocks for Str2Int conversion */
{
    proof {
        let x_val = str2int_to_int(sx@);
        let y_val = str2int_to_int(sy@);
        let m_val = str2int_to_int(sz@);
        
        let result_val = mod_exp_helper(x_val % m_val, y_val, m_val);
        
        let mut result_vec = Vec::new();
        let mut temp = result_val;
        
        while temp > 0
            invariant
                temp >= 0,
                ValidBitString(result_vec@),
                Str2Int(result_vec@) == result_val - temp * (2 as nat).pow(result_vec.len() as nat),
            decreases temp
        {
            if temp % 2 == 1 {
                result_vec.push('1');
            } else {
                result_vec.push('0');
            }
            temp = temp / 2;
        }
        
        result_vec.reverse();
        if result_vec.is_empty() {
            result_vec.push('0');
        }
        
        result_vec
    }
}
// </vc-code>

fn main() {}
}
