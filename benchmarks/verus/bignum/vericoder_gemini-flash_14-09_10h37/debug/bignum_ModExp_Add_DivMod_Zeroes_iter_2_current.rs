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
/* helper modified by LLM (iteration 2): Changed type to int for intermediate calculations and removed assume. */
spec fn AddZeroes(a: int, l: int) -> int { a * Exp_int(10int.to_nat(), l.to_nat()).to_int() }
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed type mismatches (nat vs int) and casting issues. */
{
        let x_int = Str2Int(sx@);
        let y_int = Str2Int(sy@);
        let z_int = Str2Int(sz@);

        if y_int == 0 {
            // Base case: x^0 mod z = 1 mod z
            let one_char_seq = seq!['1'];
            let one_int = Str2Int(one_char_seq);
            let result_int = one_int % z_int;
            let mut res: Vec<char> = Vec::new();
            if result_int == 0 {
                res.push('0'); // Should not happen given z_int > 1
            } else {
                let mut current = result_int;
                while current > 0 
                    invariant current >= 0,
                    decreases current
                {
                    let digit = (current % 10).to_u8();
                    res.insert(0, (b'0' + digit) as char);
                    current = (current / 10).to_nat();
                }
            }
            res
        } else {
            let exp_val = Exp_int(x_int, y_int);
            let result_val = exp_val % z_int;

            let mut res_vec: Vec<char> = Vec::new();
            if result_val == 0 {
                res_vec.push('0');
            } else {
                let mut current_val = result_val;
                while current_val > 0 
                    invariant current_val >= 0,
                    decreases current_val
                {
                    let digit = (current_val % 10).to_u8();
                    res_vec.insert(0, (b'0' + digit) as char);
                    current_val = (current_val / 10).to_nat();
                }
            }
            res_vec
        }
    }
// </vc-code>

fn main() {}
}
