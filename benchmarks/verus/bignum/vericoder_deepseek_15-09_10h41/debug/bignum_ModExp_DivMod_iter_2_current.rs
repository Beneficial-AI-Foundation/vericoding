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
proof fn exp_int_property(x: nat, y: nat, z: nat)
    requires
        z > 1,
    ensures
        Exp_int(x, y) % z == Exp_int(x % z, y) % z,
    decreases y
{
    if y > 0 {
        exp_int_property(x, (y - 1) as nat, z);
    }
}

proof fn str2int_property(s: Seq<char>, i: int)
    requires
        ValidBitString(s),
        0 <= i && i <= s.len() as int,
    ensures
        Str2Int(s.subrange(0, i)) == Str2Int(s) / Exp_int(2, (s.len() as int - i) as nat),
    decreases s.len() as int - i
{
    if i < s.len() as int {
        str2int_property(s, i + 1);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed type mismatches and added proper nat/int conversions */
    let mut x_val = Str2Int(sx@);
    let mut y_val: nat = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    let mut result: nat = 1;
    let mut base = x_val % z_val;
    
    while y_val > 0
        invariant
            result == Exp_int(x_val, y_val) % z_val,
            base == Exp_int(x_val % z_val, 1) % z_val,
        decreases y_val
    {
        if y_val as int % 2 == 1 {
            result = (result * base) % z_val;
        }
        base = (base * base) % z_val;
        y_val = (y_val as int / 2) as nat;
    }
    
    let mut res_vec = Vec::<char>::new();
    let mut temp = result;
    
    while temp > 0
        invariant
            temp >= 0,
        decreases temp
    {
        if temp as int % 2 == 1 {
            res_vec.push('1');
        } else {
            res_vec.push('0');
        }
        temp = (temp as int / 2) as nat;
    }
    
    res_vec.reverse();
    res_vec
}
// </vc-code>

fn main() {}
}
