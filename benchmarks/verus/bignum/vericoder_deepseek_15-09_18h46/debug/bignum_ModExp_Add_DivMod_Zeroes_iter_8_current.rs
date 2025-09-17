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
/* helper modified by LLM (iteration 8): Fixed Vec from_seq implementation and exp_mod_lemma parameter type */
proof fn exp_mod_lemma(x: nat, y: nat, z: nat)
    requires z > 1
    ensures Exp_int(x, y) % z == (if y == 0 { 1nat % z } else { (x * Exp_int(x, (y - 1) as nat)) % z })
{
    if y > 0 {
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
    }
}

spec fn seq_to_vec(s: Seq<char>) -> std::vec::Vec<char>
{
    s.to_vec()
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 8): Fixed Vec::from usage and type conversions */
{
    if sy.is_empty() {
        let mut result = Vec::<char>::new();
        result.push('1');
        proof {
            bitstring_cons_lemma(Seq::<char>::empty(), '1');
        }
        return result;
    }
    
    let last = sy[sy.len() - 1];
    let rest = &sy[0..sy.len() - 1];
    let rest_exp_mod = ModExp_Add_DivMod_Zeroes(sx, rest, sz);
    
    let result = if last == '1' {
        let temp_val = Str2Int(rest_exp_mod@);
        let temp_sq_val = (temp_val * temp_val) % Str2Int(sz@);
        let final_val = (temp_sq_val * Str2Int(sx@)) % Str2Int(sz@);
        let binary_seq = decimal_to_binary(final_val);
        proof {
            decimal_to_binary_valid(final_val);
            decimal_to_binary_correct(final_val);
        }
        binary_seq.to_vec()
    } else {
        let temp_val = Str2Int(rest_exp_mod@);
        let temp_sq_val = (temp_val * temp_val) % Str2Int(sz@);
        let binary_seq = decimal_to_binary(temp_sq_val);
        proof {
            decimal_to_binary_valid(temp_sq_val);
            decimal_to_binary_correct(temp_sq_val);
        }
        binary_seq.to_vec()
    };
    
    return result;
}
// </vc-code>

fn main() {}
}
