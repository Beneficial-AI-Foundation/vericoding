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
proof fn str2int_recursive(s: Seq<char>, c: char)
    requires ValidBitString(s), c == '0' || c == '1'
    ensures Str2Int(s.push(c)) == 2 * Str2Int(s) + (if c == '1' { 1nat } else { 0nat })
{
}

proof fn mod_exp_property(x: nat, y: nat, z: nat)
    requires z > 1
    ensures Exp_int(x, y) % z == Exp_int(x % z, y) % z
{
    if y > 0 {
        mod_exp_property(x, (y - 1) as nat, z);
        exp_int_recursive(x, y);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fix type errors and verification */
    if sy.is_empty() {
        proof {
            exp_int_zero_power(Str2Int(sx@));
        }
        let mut result = Vec::new();
        result.push('1');
        return result;
    }
    
    let mut x = Str2Int(sx@) % Str2Int(sz@);
    let mut y = Str2Int(sy@);
    let z = Str2Int(sz@);
    let mut result = 1;
    
    while y > 0
        invariant
            result == Exp_int(Str2Int(sx@), (Str2Int(sy@) - y) as nat) % z,
            x == Exp_int(Str2Int(sx@) % z, (Str2Int(sy@) - y + 1) as nat) % z,
            y >= 0,
        decreases y
    {
        if y % 2 == 1 {
            result = (result * x) % z;
        }
        x = (x * x) % z;
        y = y / 2;
    }
    
    let mut res_vec = Vec::new();
    let mut temp = result;
    
    while temp > 0
        invariant
            ValidBitString(res_vec@),
            Str2Int(res_vec@) == result % Exp_int(2, res_vec@.len() as nat),
            temp == result / Exp_int(2, res_vec@.len() as nat),
        decreases temp
    {
        if temp % 2 == 1 {
            res_vec.push('1');
        } else {
            res_vec.push('0');
        }
        temp = temp / 2;
    }
    
    if res_vec.is_empty() {
        res_vec.push('0');
    }
    
    res_vec.reverse();
    res_vec
}
// </vc-code>

fn main() {}
}
