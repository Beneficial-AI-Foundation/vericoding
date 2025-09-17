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
proof fn lemma_str2int_monotonic(s: Seq<char>, t: Seq<char>)
    requires
        ValidBitString(s),
        ValidBitString(t),
        s.len() == t.len(),
        forall |i: int| 0 <= i && i < s.len() ==> s[i] == '0' || s[i] == '1',
        forall |i: int| 0 <= i && i < s.len() ==> (#[trigger] s[i] as int) <= (#[trigger] t[i] as int),
    ensures
        Str2Int(s) <= Str2Int(t),
{
    if s.len() == 0 {
    } else {
        let s_prefix = s.subrange(0, s.len() as int - 1);
        let t_prefix = t.subrange(0, t.len() as int - 1);
        lemma_str2int_monotonic(s_prefix, t_prefix);
    }
}

proof fn lemma_exp_int_zero_base(x: nat, y: nat)
    requires y > 0,
    ensures Exp_int(0, y) == 0,
    decreases y,
{
    if y > 1 {
        lemma_exp_int_zero_base(0, (y - 1) as nat);
    }
}

proof fn lemma_exp_int_one_base(y: nat)
    ensures Exp_int(1, y) == 1,
    decreases y,
{
    if y > 0 {
        lemma_exp_int_one_base((y - 1) as nat);
    }
}

proof fn lemma_mod_less_than_divisor(x: nat, m: nat)
    requires m > 0,
    ensures x % m < m,
{
}

proof fn lemma_pow_mod_property(x: nat, y: nat, m: nat)
    requires m > 0,
    ensures Exp_int(x, y) % m == (x % m).pow(y) % m,
    decreases y,
{
    if y > 0 {
        lemma_pow_mod_property(x, (y - 1) as nat, m);
    }
}

spec fn to_nat(x: int) -> nat
    requires x >= 0,
{
    x as nat
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed ghost code usage by moving spec computations to proof blocks */
    proof {
        let x_val = Str2Int(sx@);
        let y_val = Str2Int(sy@);
        let z_val = Str2Int(sz@);
        let mut result_val: nat = 1;
        let mut base = x_val % z_val;
        let mut current_y = y_val;
        
        lemma_mod_less_than_divisor(result_val, z_val);
        
        while current_y > 0
            invariant
                result_val < z_val,
                Exp_int(x_val, current_y) % z_val == result_val,
            decreases current_y
        {
            if current_y % 2 == 1 {
                result_val = (result_val * base) % z_val;
            }
            base = (base * base) % z_val;
            current_y = current_y / 2;
            
            lemma_mod_less_than_divisor(result_val, z_val);
            lemma_mod_less_than_divisor(base, z_val);
        }
        
        let mut res_vec = Vec::new();
        let mut current = result_val;
        
        if current == 0 {
            res_vec.push('0');
        } else {
            while current > 0
                invariant
                    ValidBitString(res_vec@),
                    Str2Int(res_vec@) == current,
                decreases current
            {
                if current % 2 == 0 {
                    res_vec.push('0');
                } else {
                    res_vec.push('1');
                }
                current = current / 2;
            }
            res_vec.reverse();
        }
        
        res_vec
    }
}
// </vc-code>

fn main() {}
}
