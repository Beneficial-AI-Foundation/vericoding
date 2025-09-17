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

proof fn lemma_str2int_nonnegative(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) >= 0
{
    if s.len() > 0 {
        let s_prefix = s.subrange(0, s.len() as int - 1);
        lemma_str2int_nonnegative(s_prefix);
    }
}

proof fn lemma_exp_int_nonnegative(x: nat, y: nat)
    ensures Exp_int(x, y) >= 0
{
    if y > 0 {
        lemma_exp_int_nonnegative(x, (y - 1) as nat);
    }
}

proof fn lemma_power_mod(x: nat, y: nat, m: nat)
    requires m > 1
    ensures Exp_int(x, y) % m == Exp_int(x % m, y) % m
{
    if y == 0 {
    } else {
        lemma_power_mod(x, (y - 1) as nat, m);
    }
}

proof fn lemma_str2int_mod_consistency(s: Seq<char>, m: nat)
    requires ValidBitString(s), m > 1
    ensures Str2Int(s) % m == Str2Int(s) % m
{
}

proof fn lemma_bitstring_length_nonnegative(s: Seq<char>)
    requires ValidBitString(s)
    ensures s.len() >= 0
{
}

// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let mut x_val = Str2Int(sx@);
    let mut y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    
    let mut result = 1;
    let mut base = x_val % z_val;
    let mut exponent = y_val;
    
    while exponent > 0
        invariant
            result >= 0,
            base >= 0,
            exponent >= 0,
            Exp_int(x_val, y_val) % z_val == (result * Exp_int(base, exponent)) % z_val
        decreases exponent
    {
        if exponent % 2 == 1 {
            result = (result * base) % z_val;
        }
        base = (base * base) % z_val;
        exponent = exponent / 2;
    }
    
    let res_vec = Vec::new();
    if result == 0 {
        res_vec.push('0');
    } else {
        let mut temp = result;
        while temp > 0
            invariant
                temp >= 0
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
