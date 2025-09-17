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

proof fn lemma_exp_zero(x: nat)
    ensures Exp_int(x, 0) == 1
{
}

proof fn lemma_exp_rec(x: nat, y: nat)
    requires y > 0
    ensures Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat)
{
}

proof fn lemma_str2int_empty()
    ensures Str2Int(Seq::empty()) == 0
{
}

proof fn lemma_str2int_rec(s: Seq<char>)
    requires ValidBitString(s), s.len() > 0
    ensures Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
{
}

proof fn lemma_mod_exp_property(x: nat, y: nat, m: nat)
    requires m > 1
    ensures Exp_int(x, y) % m == (x % m) * Exp_int(x, (y - 1) as nat) % m when y > 0
{
}

// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let mut x_val = Str2Int(sx@);
    let mut y_val = Str2Int(sy@);
    let m = Str2Int(sz@);
    let mut result = 1nat;
    
    proof {
        lemma_exp_zero(x_val);
    }
    
    let mut i = 0;
    while i < sy@.len()
        invariant
            result == Exp_int(x_val % m, Str2Int(sy@.subrange(i, sy@.len() as int))),
            ValidBitString(sy@.subrange(i, sy@.len() as int)),
            i <= sy@.len()
        decreases sy@.len() - i
    {
        let bit = sy@[i as int];
        proof {
            lemma_str2int_rec(sy@.subrange(i, sy@.len() as int));
        }
        
        if bit == '1' {
            result = (result * (x_val % m)) % m;
        }
        
        x_val = (x_val * x_val) % m;
        i += 1;
    }
    
    let mut res_vec = Vec::new();
    if result == 0 {
        res_vec.push('0');
    } else {
        let mut temp = result;
        while temp > 0
            invariant
                temp >= 0,
                ValidBitString(res_vec@)
            decreases temp
        {
            if temp % 2 == 0 {
                res_vec.push('0');
            } else {
                res_vec.push('1');
            }
            temp = temp / 2;
        }
        res_vec.reverse();
    }
    
    res_vec
}
// </vc-code>

fn main() {}
}
