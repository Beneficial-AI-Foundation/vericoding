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
{ let mut result: Vec<char> = Vec::new();
    let mut carry: nat = 0;
    let mut i: int = 0;
    let len1 = s1.len() as int;
    let len2 = s2.len() as int;
    let max_len = if len1 > len2 { len1 } else { len2 };

    while i < max_len || carry > 0
        invariant
            carry <= 1,
            (Str2Int(s1@.subrange(0, i)) + Str2Int(s2@.subrange(0, i)) + carry) == (Str2Int(result@) + Exp_int(2, i as nat) * carry),
            ValidBitString(result@.subrange(0, i)),
            i >= 0,
        decreases max_len - i
    {
        let mut digit1: nat = 0;
        let mut digit2: nat = 0;

        if i < len1 {
            digit1 = if s1[len1 - 1 - i as nat] == '1' { 1 } else { 0 };
        }
        if i < len2 {
            digit2 = if s2[len2 - 1 - i as nat] == '1' { 1 } else { 0 };
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
    result }
// </vc-code>

// <vc-spec>
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{ let x_int = Str2Int(dividend@);
    let y_int = Str2Int(divisor@);

    let quotient_int = x_int / y_int;
    let remainder_int = x_int % y_int;

    let mut quotient_vec: Vec<char> = Vec::new();
    let mut remainder_vec: Vec<char> = Vec::new();

    if quotient_int == 0 {
        quotient_vec.push('0');
    } else {
        let mut temp_quotient = quotient_int;
        while temp_quotient > 0
            invariant
                temp_quotient >= 0,
            decreases temp_quotient
        {
            if temp_quotient % 2 == 1 {
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
        let mut temp_remainder = remainder_int;
        while temp_remainder > 0
            invariant
                temp_remainder >= 0,
            decreases temp_remainder
        {
            if temp_remainder % 2 == 1 {
                remainder_vec.insert(0, '1');
            } else {
                remainder_vec.insert(0, '0');
            }
            temp_remainder = temp_remainder / 2;
        }
    }

    (quotient_vec, remainder_vec) }
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
{ let x = Str2Int(sx@);
    let y = Str2Int(sy@);
    let z = Str2Int(sz@);

    let mut res_int: nat = 1;
    let mut base: nat = x % z;
    let mut exp: nat = y;

    while exp > 0
        invariant
            res_int < z,
            base < z,
            exp >= 0,
            Exp_int(x, y) % z == (res_int * Exp_int(base, exp)) % z,
        decreases exp
    {
        if exp % 2 == 1 {
            res_int = (res_int * base) % z;
        }
        base = (base * base) % z;
        exp = exp / 2;
    }

    let mut result_vec: Vec<char> = Vec::new();
    if res_int == 0 {
        result_vec.push('0');
    } else {
        let mut temp_res = res_int;
        while temp_res > 0
            invariant
                temp_res >= 0,
            decreases temp_res
        {
            if temp_res % 2 == 1 {
                result_vec.insert(0, '1');
            } else {
                result_vec.insert(0, '0');
            }
            temp_res = temp_res / 2;
        }
    }
    result_vec }
// </vc-code>

fn main() {}
}


