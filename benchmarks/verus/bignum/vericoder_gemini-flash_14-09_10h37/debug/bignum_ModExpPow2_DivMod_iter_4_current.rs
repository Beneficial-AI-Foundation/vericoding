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
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fixed type errors by explicitly casting `q_temp` and `r_temp` to `int` when performing arithmetic operations that return `int`, while keeping the variables as `nat` to satisfy loop conditions. */
{
    let dividend_val = Str2Int(dividend@);
    let divisor_val = Str2Int(divisor@);

    let quotient_val = dividend_val / divisor_val;
    let remainder_val = dividend_val % divisor_val;

    // Convert quotient_val to bitstring
    let mut quotient_vec: Vec<char> = Vec::new();
    let mut q_temp: nat = quotient_val;
    if q_temp == 0 {
        quotient_vec.insert(0, '0');
    } else {
        while q_temp > 0 {
            if (q_temp as int) % 2 == 0 {
                quotient_vec.insert(0, '0');
            } else {
                quotient_vec.insert(0, '1');
            }
            q_temp = (q_temp as int / 2) as nat;
        }
    }

    // Convert remainder_val to bitstring
    let mut remainder_vec: Vec<char> = Vec::new();
    let mut r_temp: nat = remainder_val;
    if r_temp == 0 {
        remainder_vec.insert(0, '0');
    } else {
        while r_temp > 0 {
            if (r_temp as int) % 2 == 0 {
                remainder_vec.insert(0, '0');
            } else {
                remainder_vec.insert(0, '1');
            }
            r_temp = (r_temp as int / 2) as nat;
        }
    }

    (quotient_vec, remainder_vec)
}
// </vc-code>

// <vc-spec>
exec fn ModExpPow2(sx: &[char], sy: &[char], n: int, sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    n >= 0,
    (Str2Int(sy@) == Exp_int(2, n as nat) || Str2Int(sy@) == 0),
    sy@.len() == (n as nat) + 1,
    Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases n
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fixed type errors by explicitly casting `sy@.len()` and `r_temp` to `int` when performing arithmetic operations that return `int` or when an `int` is expected, while keeping the variables as `nat` for loop conditions. Also addressed array indexing error. */
{
    let zero_char_vec = { let mut v = Vec::new(); v.push('0'); v };
    let one_char_vec = { let mut v = Vec::new(); v.push('1'); v };

    if n == 0 {
        if Str2Int(sy@) == 0 {
            // Exp_int(X, 0) == 1
            let one: nat = Str2Int(one_char_vec@);
            let sz_val: nat = Str2Int(sz@);
            let result_val: nat = one % sz_val;

            let mut result_vec: Vec<char> = Vec::new();
            let mut r_temp: nat = result_val;
            if r_temp == 0 {
                result_vec.insert(0, '0');
            } else {
                while r_temp > 0 {
                    if (r_temp as int) % 2 == 0 {
                        result_vec.insert(0, '0');
                    } else {
                        result_vec.insert(0, '1');
                    }
                    r_temp = (r_temp as int / 2) as nat;
                }
            }

            result_vec
        } else { // Str2Int(sy@) == 1 (as n=0, Exp_int(2,0) = 1)
            // Exp_int(X, 1) == X
            let sx_val: nat = Str2Int(sx@);
            let sz_val: nat = Str2Int(sz@);
            let result_val: nat = sx_val % sz_val;

            let mut result_vec: Vec<char> = Vec::new();
            let mut r_temp: nat = result_val;
            if r_temp == 0 {
                result_vec.insert(0, '0');
            } else {
                while r_temp > 0 {
                    if (r_temp as int) % 2 == 0 {
                        result_vec.insert(0, '0');
                    } else {
                        result_vec.insert(0, '1');
                    }
                    r_temp = (r_temp as int / 2) as nat;
                }
            }
            result_vec
        }
    } else {
        let sx_val: nat = Str2Int(sx@);
        let sy_val: nat = Str2Int(sy@);
        let sz_val: nat = Str2Int(sz@);

        let mut half_sy_vec = Vec::new();
        for i in 0..(sy@.len() as int - 1) {
            half_sy_vec.push(sy@.index(i));
        }

        let r_prev_vec = ModExpPow2(sx, &half_sy_vec, n - 1, sz);
        let r_prev_val: nat = Str2Int(r_prev_vec@);

        if (sy_val as int) % 2 == 0 {
            // If sy is even, (X^(y/2))^2 mod Z
            let result_val: nat = (r_prev_val * r_prev_val) % sz_val;

            let mut result_vec: Vec<char> = Vec::new();
            let mut r_temp: nat = result_val;
            if r_temp == 0 {
                result_vec.insert(0, '0');
            } else {
                while r_temp > 0 {
                    if (r_temp as int) % 2 == 0 {
                        result_vec.insert(0, '0');
                    } else {
                        result_vec.insert(0, '1');
                    }
                    r_temp = (r_temp as int / 2) as nat;
                }
            }
            result_vec
        } else {
            // If sy is odd, X * (X^(y/2))^2 mod Z
            let result_val: nat = (sx_val * r_prev_val * r_prev_val) % sz_val;

            let mut result_vec: Vec<char> = Vec::new();
            let mut r_temp: nat = result_val;
            if r_temp == 0 {
                result_vec.insert(0, '0');
            } else {
                while r_temp > 0 {
                    if (r_temp as int) % 2 == 0 {
                        result_vec.insert(0, '0');
                    }
                    else {
                        result_vec.insert(0, '1');
                    }
                    r_temp = (r_temp as int / 2) as nat;
                }
            }
            result_vec
        }
    }
}
// </vc-code>

fn main() {}
}


