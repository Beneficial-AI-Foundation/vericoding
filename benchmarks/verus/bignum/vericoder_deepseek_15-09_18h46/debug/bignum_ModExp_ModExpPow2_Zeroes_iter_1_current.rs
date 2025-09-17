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
proof fn exp_int_recursive_property(x: nat, y: nat)
    requires
        y > 0,
    ensures
        Exp_int(x, y) == x * Exp_int(x, y - 1)
{
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
    if sy.is_empty() {
        proof {
            exp_int_recursive_property(Str2Int(sx@), 0);
        }
        return vec!['1'];
    }
    
    let y_tail = &sy[..sy.len() - 1];
    let y_last = sy[sy.len() - 1];
    
    let mut result: Vec<char> = vec![];
    
    if y_last == '1' {
        let base_result = ModExp_ModExpPow2_Zeroes(sx, y_tail, sz);
        result = base_result;
        result.push('1');
    } else {
        let base_result = ModExp_ModExpPow2_Zeroes(sx, y_tail, sz);
        result = base_result;
        result.push('0');
    }
    
    result
}
// </vc-code>

fn main() {}
}
