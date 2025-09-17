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
/* helper modified by LLM (iteration 4): ensure `exp - 1` is `nat` */
spec fn ModExp_ModExpPow2_Mul_helper(base: nat, exp: nat, modulus: nat) -> nat
    decreases exp
{
    if exp == 0 {
        1
    } else if exp % 2 == 0 {
        let half_exp_result = ModExp_ModExpPow2_Mul_helper(base, exp / 2, modulus);
        (half_exp_result * half_exp_result) % modulus
    } else {
        (base * ModExp_ModExpPow2_Mul_helper(base, (exp - 1) as nat, modulus)) % modulus
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Cast literals to `nat` where needed */
{
    let base_val = Str2Int(sx@);
    let exp_val = Str2Int(sy@);
    let modulus_val = Str2Int(sz@);
    let result_nat = ModExp_ModExpPow2_Mul_helper(base_val, exp_val, modulus_val);

    let mut digits: Vec<char> = Vec::new();
    if result_nat == 0nat {
        digits.push('0');
    } else {
        let mut temp = result_nat;
        while temp > 0nat
            invariant
                temp >= 0nat,
        {
            if (temp % 2nat) == 1nat {
                digits.push('1');
            } else {
                digits.push('0');
            }
            temp = temp / 2nat;
        }
    }
    digits.reverse();
    digits
}
// </vc-code>

fn main() {}
}
