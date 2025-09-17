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
    if y > 1 {
        exp_int_recursive_property(x, y - 1);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed type conversion issue */
{
    if sy.len() == 0 {
        let res: Vec<char> = vec!['1'];
        return res;
    }
    
    let y_tail = &sy[..sy.len() - 1];
    let y_last = sy[sy.len() - 1];
    
    let mut base_result = ModExp_ModExpPow2_Zeroes(sx, y_tail, sz);
    
    if y_last == '1' {
        base_result.push('1');
    } else {
        base_result.push('0');
    }
    
    base_result
}
// </vc-code>

fn main() {}
}
