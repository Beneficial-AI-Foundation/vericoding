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
proof fn helper_lemma_exp_base(x: nat, y: nat) ensures Exp_int(x, y) % x == 0 when y > 0 decreases y { if y > 0 { helper_lemma_exp_base(x, (y - 1) as nat); } }
proof fn helper_lemma_exp_zero(y: nat) ensures Exp_int(0, y) == 0 when y > 0 decreases y { if y > 0 { helper_lemma_exp_zero((y - 1) as nat); } }
proof fn helper_lemma_one_mod_z(z: nat) requires z > 1 ensures 1 % z == 1 {}
proof fn helper_lemma_str2int_empty() ensures Str2Int(Seq::<char>::empty()) == 0 {}
proof fn helper_lemma_exp_property(x: nat, y: nat, z: nat) requires z > 1 ensures Exp_int(x, y) % z == ((x % z) * (Exp_int(x, (y - 1) as nat) % z)) % z when y > 0 decreases y { if y > 0 { helper_lemma_exp_property(x, (y - 1) as nat, z); } }
// </vc-helpers>

// <vc-spec>
exec fn ModExp_int_ModExpPow2_int(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Fixed syntax error in proof lemma calls */
    let x_val = Str2Int(sx@);
    let mut y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    let mut result = 1;
    let mut base = x_val % z_val;
    
    while y_val > 0
        invariant
            result * Exp_int(base, y_val) % z_val == Exp_int(x_val, y_val) % z_val
        decreases y_val
    {
        if y_val % 2 == 1 {
            result = (result * base) % z_val;
        }
        base = (base * base) % z_val;
        y_val = y_val / 2;
    }
    
    proof { helper_lemma_one_mod_z(z_val); }
    
    let mut char_vec = Vec::new();
    char_vec.push(if result == 1 { '1' } else { '0' });
    
    char_vec
}
// </vc-code>

fn main() {}
}
