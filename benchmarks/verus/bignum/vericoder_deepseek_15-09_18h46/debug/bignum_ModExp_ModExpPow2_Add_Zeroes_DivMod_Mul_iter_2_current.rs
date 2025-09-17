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
/* helper modified by LLM (iteration 2): fix nat literals and type annotations */
proof fn exp_int_recursive_lemma(x: nat, y: nat)
    ensures
        Exp_int(x, y) == if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
{
    if y > 0 {
        exp_int_recursive_lemma(x, (y - 1) as nat);
    }
}

proof fn str2int_recursive_lemma(s: Seq<char>)
    requires
        ValidBitString(s),
    ensures
        s.len() == 0 ==> Str2Int(s) == 0,
        s.len() > 0 ==> Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1 } else { 0 })
{
    if s.len() > 0 {
        str2int_recursive_lemma(s.subrange(0, s.len() as int - 1));
    }
}

proof fn valid_bitstring_subrange_lemma(s: Seq<char>, start: int, end: int)
    requires
        ValidBitString(s),
        0 <= start,
        end <= s.len() as int,
        start <= end,
    ensures
        ValidBitString(s.subrange(start, end))
{
}

proof fn valid_bitstring_append_lemma(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
    ensures
        ValidBitString(s1 + s2)
{
}

proof fn mod_exp_property_lemma(base: nat, exp: nat, modulus: nat)
    requires
        modulus > 1,
    ensures
        Exp_int(base, exp) % modulus == if exp == 0 { 1 % modulus } else { (base * (Exp_int(base, (exp - 1) as nat) % modulus)) % modulus }
{
    if exp > 0 {
        exp_int_recursive_lemma(base, exp);
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
/* code modified by LLM (iteration 2): fix nat type issues and compilation errors */
{
    let x_val: nat = Str2Int(sx@);
    let y_val: nat = Str2Int(sy@);
    let z_val: nat = Str2Int(sz@);
    let mut result_val: nat = 1;
    
    let mut current_exp: nat = y_val;
    
    while current_exp > 0
        invariant
            result_val == Exp_int(x_val, (y_val - current_exp) as nat) % z_val,
            current_exp >= 0,
        decreases current_exp
    {
        proof {
            mod_exp_property_lemma(x_val, current_exp, z_val);
        }
        
        result_val = (x_val * result_val) % z_val;
        current_exp = current_exp - 1;
    }
    
    let mut res_vec = Vec::new();
    if result_val == 1 {
        res_vec.push('1');
    } else {
        res_vec.push('0');
    }
    
    res_vec
}
// </vc-code>

fn main() {}
}
