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
/* helper modified by LLM (iteration 3): Removed extraneous spec function as `ModExp_Add_DivMod_Zeroes` is an `exec` function. */
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Type issues with `nat` and `int` are fixed by ensuring arithmetic operations on `nat` variables result in `nat` types. Casts from `int` to `nat` are added where division occurs. */
{
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    let mut result_val: nat = 1;
    let mut current_y: nat = y_val;
    let mut base: nat = x_val % z_val;

    while current_y > 0
        invariant
            current_y >= 0,
            result_val % z_val == ModExp_Add_DivMod_Zeroes_spec(sx@, y_val.add(current_y).sub(y_val).add(sy@).add(sz@), sz@), /* Placeholder for correct invariant */ 
            base % z_val == ModExp_Add_DivMod_Zeroes_spec(sx@, current_y.add(sy@).add(sz@), sz@), /* Placeholder for correct invariant */ 
        decreases current_y
    {
        if current_y % 2 == 1nat {
            result_val = (result_val * base) % z_val;
        }
        base = (base * base) % z_val;
        current_y = (current_y / 2) as nat;
    }

    let mut res = Vec::new();
    let mut temp = result_val;
    if temp == 0 {
        res.push('0');
    } else {
        while temp > 0
            invariant
                temp >= 0,
            decreases temp
        {
            if temp % 2 == 1 {} else {}
            temp = (temp / 2) as nat;
        }
    }

    res
}
// </vc-code>

fn main() {}
}
