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
/* helper modified by LLM (iteration 4): Fix literal types and ensure nat compatibility */
proof fn lemma_str2int_concat_proof(s: Seq<char>, c: char)
    requires ValidBitString(s), c == '0' || c == '1'
    ensures Str2Int(s.push(c)) == 2 * Str2Int(s) + (if c == '1' {1nat} else {0nat})
{
    if s.len() > 0 {
        let s_prefix = s.subrange(0, s.len() as int - 1);
        lemma_str2int_concat_proof(s_prefix, s.index(s.len() as int - 1));
    }
}

proof fn lemma_mod_bound(x: nat, d: nat)
    requires d > 1
    ensures 0 <= x % d && x % d < d
{
}

proof fn lemma_exp_int_positive(x: nat, y: nat) 
    ensures Exp_int(x, y) >= 1
{
    if y == 0 {
    } else {
        lemma_exp_int_positive(x, (y - 1) as nat);
    }
}

proof fn lemma_str2int_nonnegative(s: Seq<char>) 
    requires ValidBitString(s)
    ensures Str2Int(s) >= 0
{
    if s.len() > 0 {
        let s_prefix = s.subrange(0, s.len() as int - 1);
        lemma_str2int_nonnegative(s_prefix);
    }
}

proof fn lemma_nat_conversions()
{
}

fn to_nat(n: int) -> nat
    requires n >= 0
    ensures result == n
{
    n as nat
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Fix nat vs int type mismatches and ensure proper arithmetic */
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    
    let mut result_val: nat = 1nat;
    let mut current_exp: nat = y_val;
    let mut base: nat = x_val % z_val;
    
    lemma_exp_int_positive(x_val, y_val);
    lemma_mod_bound(base, z_val);
    
    while current_exp > 0nat
        invariant
            result_val * Exp_int(base, current_exp) % z_val == Exp_int(x_val, y_val) % z_val,
            result_val < z_val,
            current_exp >= 0nat
        decreases current_exp
    {
        if current_exp % 2nat == 1nat {
            result_val = (result_val as int * base as int % z_val as int) as nat;
        }
        base = (base as int * base as int % z_val as int) as nat;
        current_exp = current_exp / 2nat;
    }
    
    assert(result_val == Exp_int(x_val, y_val) % z_val);
    let mut result_vec = Vec::<char>::new();
    let mut temp = result_val;
    
    if temp == 0nat {
        result_vec.push('0');
    } else {
        while temp > 0nat
            invariant
                ValidBitString(result_vec@),
                Str2Int(result_vec@) == temp
            decreases temp
        {
            let bit = if temp % 2nat == 1nat { '1' } else { '0' };
            result_vec.push(bit);
            temp = temp / 2nat;
        }
        result_vec.reverse();
    }
    
    result_vec
}
// </vc-code>

fn main() {}
}
