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
/* helper modified by LLM (iteration 2): Fix return type and add ghost variable for nat conversion */
spec fn bitstring_to_nat(s: Seq<char>) -> nat
    recommends ValidBitString(s)
{
    Str2Int(s)
}

proof fn helper_lemma_exp_mod_result(x: nat, y: nat, m: nat)
    requires m > 1
    ensures Exp_int(x, y) % m == Exp_int(x % m, y) % m
    decreases y
{
    if y > 0 {
        helper_lemma_exp_mod_result(x, y - 1, m);
        helper_lemma_mod_properties(x, Exp_int(x, y - 1), m);
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
/* code modified by LLM (iteration 2): Fix variable scoping and type conversion */
{
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    
    proof {
        helper_lemma_exp_mod_result(x_val, y_val, z_val);
    }
    
    let mod_result: nat = Exp_int(x_val % z_val, y_val) % z_val;
    ghost {
        let result_bits = nat_to_bitstring(mod_result);
    }
    let result_bits = nat_to_bitstring(mod_result);
    
    let mut result_vec = Vec::<char>::new();
    let mut i: usize = 0;
    while i < result_bits.len()
        invariant
            i <= result_bits.len(),
            result_vec@ == result_bits.subrange(0, i as int),
            ValidBitString(result_vec@)
        decreases result_bits.len() - i
    {
        result_vec.push(result_bits.index(i as int));
        i += 1;
    }
    
    result_vec
}
// </vc-code>

fn main() {}
}
