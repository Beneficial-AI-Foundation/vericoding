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
    ensures Str2Int(Seq::<char>::empty()) == 0
{
}

proof fn lemma_str2int_rec(s: Seq<char>, c: char)
    requires s.len() > 0, ValidBitString(s.push(c))
    ensures Str2Int(s.push(c)) == 2 * Str2Int(s) + (if c == '1' { 1 } else { 0 })
{
}

proof fn lemma_mod_exp_property(x: nat, y: nat, z: nat)
    requires z > 1
    ensures Exp_int(x, y) % z == Exp_int(x % z, y) % z
{
}

// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
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
    
    proof {
        lemma_mod_exp_property(x_val, y_val, z_val);
    }
    
    while y_val > 0
        invariant
            result == Exp_int(x_val % z_val, y_val) % z_val,
        decreases y_val
    {
        if y_val % 2 == 1 {
            result = (result * x_val) % z_val;
        }
        x_val = (x_val * x_val) % z_val;
        y_val = y_val / 2;
    }
    
    let mut res_vec = Vec::<char>::new();
    let mut temp = result;
    
    while temp > 0
        invariant
            ValidBitString(res_vec@),
            Str2Int(res_vec@) == temp,
        decreases temp
    {
        if temp % 2 == 1 {
            res_vec.push('1');
        } else {
            res_vec.push('0');
        }
        temp = temp / 2;
    }
    
    res_vec.reverse();
    if res_vec.is_empty() {
        res_vec.push('0');
    }
    
    res_vec
}
// </vc-code>

fn main() {}
}
