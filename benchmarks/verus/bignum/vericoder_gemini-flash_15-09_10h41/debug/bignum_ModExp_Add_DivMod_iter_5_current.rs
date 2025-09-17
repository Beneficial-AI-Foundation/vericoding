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

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected `while` loop invariant termination measure. */
{
    let mut result: Vec<char> = Vec::new();
    let mut carry: u8 = 0;
    let mut i: usize = 0;
    let len1_int: usize = s1@.len();
    let len2_int: usize = s2@.len();
    let max_len_int: usize = if len1_int > len2_int { len1_int } else { len2_int };

    while i < max_len_int || carry > 0
        invariant
            carry == 0 || carry == 1,
            ValidBitString(result@),
            i <= max_len_int + 1 // Added to ensure i does not exceed maximum possible value
        decreases max_len_int + 1 - i
    {
        let mut digit1: u8 = 0;
        let mut digit2: u8 = 0;

        if i < len1_int {
            digit1 = if s1[len1_int - 1 - i] == '1' { 1 } else { 0 };
        }
        if i < len2_int {
            digit2 = if s2[len2_int - 1 - i] == '1' { 1 } else { 0 };
        }

        let sum_digits = digit1 + digit2 + carry;
        let current_digit = sum_digits % 2;
        carry = sum_digits / 2;

        if current_digit == 1 {
            result.insert(0, '1');
        } else {
            result.insert(0, '0');
        }
        i = i + 1;
    }

    if result.len() == 0 {
        result.push('0');
    }
    result
}
// </vc-code>

// <vc-spec>
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Modified `DivMod` to avoid direct `nat` operations. */
{
    let x_int = Str2Int(dividend@);
    let y_int = Str2Int(divisor@);

    let quotient_int: nat = x_int / y_int;
    let remainder_int: nat = x_int % y_int;

    let mut quotient_vec: Vec<char> = Vec::new();
    let mut remainder_vec: Vec<char> = Vec::new();

    if quotient_int == 0 {
        quotient_vec.push('0');
    } else {
        let mut temp_quotient: nat = quotient_int;
        while temp_quotient > 0
            invariant
                temp_quotient >= 0,
            decreases temp_quotient
        {
            if (temp_quotient % 2) == 1 {
                quotient_vec.insert(0, '1');
            } else {
                quotient_vec.insert(0, '0');
            }
            temp_quotient = temp_quotient / 2;
        }
    }

    if remainder_int == 0 {
        remainder_vec.push('0');
    } else {
        let mut temp_remainder: nat = remainder_int;
        while temp_remainder > 0
            invariant
                temp_remainder >= 0,
            decreases temp_remainder
        {
            if (temp_remainder % 2) == 1 {
                remainder_vec.insert(0, '1');
            } else {
                remainder_vec.insert(0, '0');
            }
            temp_remainder = temp_remainder / 2;
        }
    }

    (quotient_vec, remainder_vec)
}
// </vc-code>

// <vc-spec>
exec fn ModExp(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Changed ghost variable `res_int` to tracked `res_int_ghost` and `base_ghost`, and `result_vec` which makes the code compatible to Verus. Also casted values to `u128` to avoid mixing ghost and non-ghost type. */
{
    let x = Str2Int(sx@);
    let y = Str2Int(sy@);
    let z = Str2Int(sz@);

    let mut result_vec: Vec<char> = Vec::new();

    let mut res_int_ghost: nat = 1; // Ghost variable for intermediate computation logic
    let mut base_ghost: nat = x % z;
    let mut exp_ghost: nat = y;

    let mut res_exec: u128 = 1; // Executable variable for intermediate computation logic
    let mut base_exec: u128 = (x % z) as u128;
    let mut exp_exec: u128 = y as u128;

    while exp_exec > 0
        invariant
            exp_exec >= 0,
            base_exec < z as u128,
            res_exec < z as u128,
            res_int_ghost == (res_exec as nat),
            base_ghost == (base_exec as nat),
            exp_ghost == (exp_exec as nat),
            Exp_int(x, y) % z == (res_int_ghost * Exp_int(base_ghost, exp_ghost)) % z
        decreases exp_exec
    {
        if (exp_exec % 2) == 1 {
            res_exec = (res_exec * base_exec) % (z as u128);
            res_int_ghost = (res_int_ghost * base_ghost) % z;
        }
        base_exec = (base_exec * base_exec) % (z as u128);
        base_ghost = (base_ghost * base_ghost) % z;
        exp_exec = exp_exec / 2;
        exp_ghost = exp_ghost / 2; // Keep ghost variable in sync
    }

    if res_exec == 0 {
        result_vec.push('0');
    } else {
        let mut temp_res = res_exec;
        while temp_res > 0
            invariant
                temp_res >= 0
            decreases temp_res
        {
            if (temp_res % 2) == 1 {
                result_vec.insert(0, '1');
            } else {
                result_vec.insert(0, '0');
            }
            temp_res = temp_res / 2;
        }
    }
    result_vec
}
// </vc-code>

fn main() {}
}


