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
/* helper modified by LLM (iteration 3): Removed type suffix for literals */
spec fn ModExp(x: nat, y: nat, z: nat) -> nat
decreases y
{
    if y == 0 { 1 } else if y == 1 { x % z } else {
        let half_y = ModExp(x, y / 2, z);
        let mut result = (half_y * half_y) % z;
        if y % 2 == 1 {
            result = (result * (x % z)) % z;
        }
        result
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed integer literal suffixes and Seq::singleton usage */
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);

    let result_nat = ModExp(x_int, y_int, z_int);

    let result_str = if result_nat == 0 {
        vstd::seq::Seq::new(1, |i: nat| '0')
    } else {
        let mut temp_val: nat = result_nat;
        let mut digits = vstd::seq::Seq::new(0, |i: nat| '0');
        while temp_val > 0
            invariant
                temp_val >= 0,
                forall |i| 0 <= i && i < digits.len() ==> (digits.index(i) == '0' || digits.index(i) == '1'),
            decreases temp_val
        {
            let rem: nat = temp_val % 2;
            digits = digits.push(if rem == 1 { '1' } else { '0' });
            temp_val = temp_val / 2;
        }
        digits.reverse()
    };

    result_str.to_vec()
}
// </vc-code>

fn main() {}
}
