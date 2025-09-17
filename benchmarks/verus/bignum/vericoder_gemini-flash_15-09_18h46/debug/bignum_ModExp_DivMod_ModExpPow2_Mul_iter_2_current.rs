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
/* helper modified by LLM (iteration 2): Introduced nat_to_char_vec as a spec function instead of a proof function. */
spec fn nat_to_char_vec_spec(n: nat) -> Seq<char>
    ensures
        ValidBitString(result),
        Str2Int(result) == n,
        result.len() >= 1 || n == 0
{
    if n == 0 {
        seq!['0']
    } else {
        let mut digits: Seq<char> = Seq::empty();
        let mut temp_n = n;
        while temp_n > 0
            invariant
                temp_n >= 0,
                forall |i: int| 0 <= i && i < digits.len() ==> (digits[i] == '0' || digits[i] == '1'),
                temp_n * (2_nat.pow(digits.len() as nat)) + Str2Int(digits) == n
            decreases temp_n
        {
            let remainder = temp_n % 2;
            if remainder == 0 {
                digits = seq!['0'].add(digits);
            } else {
                digits = seq!['1'].add(digits);
            }
            temp_n = temp_n / 2;
        }
        digits
    }
}

// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed variable visibility and type issues. */
{
    let x_val = Str2Value(sx);
    let y_val = Str2Value(sy);
    let z_val = Str2Value(sz);

    if y_val == 0 {
        let one_vec: Vec<char> = vec!['1'];
        one_vec
    } else if y_val == 1 {
        sx.to_vec()
    } else {
        let y_minus_1_val = (y_val - 1);
        let sy_minus_1_seq = nat_to_char_vec_spec(y_minus_1_val);
        let sy_minus_1_vec = sy_minus_1_seq.to_vec();

        let recursive_result_vec = ModExp_DivMod_ModExpPow2_Mul(sx, sy_minus_1_vec.as_slice(), sz);
        let recursive_result_val = Str2Value(recursive_result_vec.as_slice());

        let current_product = (x_val * recursive_result_val) % z_val;

        nat_to_char_vec_spec(current_product).to_vec()
    }
}
// </vc-code>

fn main() {}
}
