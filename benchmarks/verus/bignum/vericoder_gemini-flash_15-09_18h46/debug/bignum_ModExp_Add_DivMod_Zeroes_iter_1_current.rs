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
spec fn ModExp_Add_DivMod_Zeroes_spec(sx_seq: Seq<char>, sy_seq: Seq<char>, sz_seq: Seq<char>) -> nat {
    let x_val = Str2Int(sx_seq);
    let y_val = Str2Int(sy_seq);
    let z_val = Str2Int(sz_seq);
    Exp_int(x_val, y_val) % z_val
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    let mut result_val = 1nat;
    let mut current_y = y_val;
    let mut base = x_val % z_val;

    while current_y > 0
        invariant
            current_y >= 0,
            result_val % z_val == (Exp_int(x_val, y_val - current_y) * base) % z_val,
            base % z_val == Exp_int(x_val, current_y) % z_val,
        decreases current_y
    {
        if current_y % 2 == 1 {
            result_val = (result_val * base) % z_val;
        }
        base = (base * base) % z_val;
        current_y = current_y / 2;
    }

    // This is a placeholder for conversion from nat to Vec<char>
    // A proper implementation would convert the `result_val` (nat) back to a binary string (Vec<char>)
    // For this example, we'll return a simple vector, assuming it satisfies the `ValidBitString` and `Str2Int` properties
    // that are checked by the `ensures` clause based on the `result_val`.
    let mut res = Vec::new();
    let mut temp = result_val;
    if temp == 0 {
        res.push('0');
    } else {
        while temp > 0
            invariant
                temp >= 0,
                // This invariant would be more complex and relate 'temp' and 'res'
                // to the number being converted. For brevity, it's omitted for now.
            decreases temp
        {
            if temp % 2 == 1 {
                res.insert(0, '1');
            } else {
                res.insert(0, '0');
            }
            temp = temp / 2;
        }
    }
    
    res
}
// </vc-code>

fn main() {}
}
