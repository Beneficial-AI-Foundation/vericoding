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
/* helper modified by LLM (iteration 7): Removed helper which was causing build issues */
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 7): Changed `Vec::len()` to return `usize` to be compatible with `as int` conversion. */
{
    let x_val_u64: u64 = Str2Int(sx@) as u64;
    let y_val_u64: u64 = Str2Int(sy@) as u64;
    let z_val_u64: u64 = Str2Int(sz@) as u64;

    let mut result_val_u64: u64 = 1;
    let mut current_y_u64: u64 = y_val_u64;
    let mut base_u64: u64 = x_val_u64 % z_val_u64;

    while current_y_u64 > 0
        invariant
            z_val_u64 > 1,
            (result_val_u64 as nat * Exp_int(base_u64 as nat, current_y_u64 as nat)) % z_val_u64 as nat == Exp_int(x_val_u64 as nat, y_val_u64 as nat) % z_val_u64 as nat,
            base_u64 < z_val_u64,
            result_val_u64 < z_val_u64,
        decreases current_y_u64
    {
        if current_y_u64 % 2 == 1 {
            result_val_u64 = (result_val_u64 * base_u64) % z_val_u64;
        }
        base_u64 = (base_u64 * base_u64) % z_val_u64;
        current_y_u64 = current_y_u64 / 2;
    }

    let mut res = Vec::new();
    let mut temp_u64: u64 = result_val_u64;
    if temp_u64 == 0 {
        res.push('0');
    } else {
        let mut bits: Vec<char> = Vec::new();
        while temp_u64 > 0
            invariant
                temp_u64 >= 0,
            decreases temp_u64
        {
            if temp_u64 % 2 == 1 {
                bits.push('1');
            } else {
                bits.push('0');
            }
            temp_u64 = temp_u64 / 2;
        }
        let mut i: int = bits.len() as int - 1;
        while i >= 0
            invariant
                i >= -1,
                i < bits.len() as int,
            decreases i
        {
            res.push(bits[i as usize]);
            i = i - 1;
        }
    }

    res
}
// </vc-code>

fn main() {}
}
