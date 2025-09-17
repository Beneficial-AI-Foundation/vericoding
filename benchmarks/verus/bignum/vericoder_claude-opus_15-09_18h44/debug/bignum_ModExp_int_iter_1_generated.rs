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
spec fn mod_exp_helper(x: nat, y: nat, z: nat) -> nat
    recommends z > 1
    decreases y
{
    if y == 0 {
        1 % z
    } else if y % 2 == 0 {
        let half = mod_exp_helper(x, y / 2, z);
        (half * half) % z
    } else {
        (x * mod_exp_helper(x, (y - 1) as nat, z)) % z
    }
}

proof fn mod_exp_correct(x: nat, y: nat, z: nat)
    requires z > 1
    ensures mod_exp_helper(x, y, z) == Exp_int(x, y) % z
    decreases y
{
    if y == 0 {
    } else if y % 2 == 0 {
        mod_exp_correct(x, y / 2, z);
        assert(Exp_int(x, y) == Exp_int(x, y / 2) * Exp_int(x, y / 2));
    } else {
        mod_exp_correct(x, (y - 1) as nat, z);
    }
}

exec fn int_to_bitstring(n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@),
            Str2Int(res@) == n
{
    let mut result = Vec::new();
    let mut num = n;
    
    if num == 0 {
        result.push('0');
        return result;
    }
    
    while num > 0
        invariant
            ValidBitString(result@),
            num * Exp_int(2, result.len() as nat) + Str2Int(result@) == n
    {
        if num % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        num = num / 2;
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_int(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    
    let result_val = mod_exp_helper(x_val, y_val, z_val);
    
    proof {
        mod_exp_correct(x_val, y_val, z_val);
    }
    
    let res = int_to_bitstring(result_val);
    res
}
// </vc-code>

fn main() {}
}
