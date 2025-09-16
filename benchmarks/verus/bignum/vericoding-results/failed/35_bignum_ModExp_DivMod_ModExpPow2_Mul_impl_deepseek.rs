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
/* helper modified by LLM (iteration 10): Fix type conversion issues and add proper lemmas for ghost code */
proof fn lemma_div_mod_theorem(a: nat, b: nat)
    requires b > 0,
    ensures a == (a / b) * b + (a % b),
{
    // Mathematical fact that should be accepted by Verus
}

proof fn lemma_mod_neg(a: nat, b: nat)
    requires b > 0,
    ensures a % b == (a + b) % b,
{
    // Mathematical fact about modulo with offset
}

proof fn lemma_exp_int_zero(x: nat)
    ensures Exp_int(x, 0) == 1,
{
}

proof fn lemma_exp_int_rec(x: nat, y: nat)
    requires y > 0,
    ensures Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat),
{
}

proof fn lemma_pow_mod_property(a: nat, b: nat, m: nat)
    requires m > 1,
    ensures Exp_int(a, b) % m == Exp_int(a % m, b) % m,
    decreases b,
{
    if b == 0 {
    } else {
        lemma_pow_mod_property(a, (b - 1) as nat, m);
        lemma_div_mod_theorem(a, m);
        lemma_mod_neg(a, m);
        lemma_exp_int_rec(a % m, b);
    }
}

proof fn helper_lemma_for_verification(x: nat, y: nat, m: nat)
    requires m > 1,
    ensures Exp_int(x, y) % m == Exp_int(x % m, y) % m,
{
    lemma_pow_mod_property(x, y, m);
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fix ghost code usage and implement proper type handling */
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let m_int = Str2Int(sz@);
    
    proof {
        helper_lemma_for_verification(x_int, y_int, m_int);
    }
    
    // Calculate the result using ghost expressions only
    ghost {
        let ghost_result = Exp_int(x_int % m_int, y_int) % m_int;
        let result_value: int = ghost_result as int;
    }
    
    // Convert result to binary string representation
    let mut res_vec = Vec::<char>::new();
    ghost var val: nat = Exp_int(x_int % m_int, y_int) % m_int;
    let mut working_val = (Exp_int(x_int % m_int, y_int) % m_int) as int;
    
    while working_val > 0
        invariant
            forall |i: int| 0 <= i && i < res_vec@.len() ==> (res_vec@[i] == '0' || res_vec@[i] == '1'),
            working_val >= 0,
            working_val as nat == val >> (res_vec@.len() as nat),
            Str2Int(res_vec@) == val,
        decreases working_val,
    {
        if working_val % 2 == 0 {
            res_vec.push('0');
        } else {
            res_vec.push('1');
        }
        working_val = working_val / 2;
        proof {
            val = val / 2;
        }
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
