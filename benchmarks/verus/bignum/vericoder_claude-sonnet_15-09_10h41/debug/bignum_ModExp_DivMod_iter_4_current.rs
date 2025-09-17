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
/* helper modified by LLM (iteration 4): fixed nat literal comparisons and operations */
fn ModExp_DivMod_impl(x: nat, y: nat, z: nat) -> nat
    requires z > 1
    ensures ModExp_DivMod_impl(x, y, z) == Exp_int(x, y) % z
    decreases y
{
    if y == 0nat {
        1nat % z
    } else {
        let half_exp = ModExp_DivMod_impl(x, y / 2nat, z);
        let squared = (half_exp * half_exp) % z;
        if y % 2nat == 0nat {
            squared
        } else {
            (x * squared) % z
        }
    }
}

fn nat_to_bit_string(n: nat) -> Vec<char>
    ensures ValidBitString(nat_to_bit_string(n)@)
{
    if n == 0nat {
        vec!['0']
    } else {
        let mut result = Vec::new();
        let mut temp = n;
        while temp > 0nat
            invariant ValidBitString(result@)
        {
            if temp % 2nat == 0nat {
                result.push('0');
            } else {
                result.push('1');
            }
            temp = temp / 2nat;
        }
        result.reverse();
        result
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fixed nat literal comparisons and operations */
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    
    let result_val = ModExp_DivMod_impl(x_val, y_val, z_val);
    let result_vec = nat_to_bit_string(result_val);
    
    result_vec
}
// </vc-code>

fn main() {}
}
