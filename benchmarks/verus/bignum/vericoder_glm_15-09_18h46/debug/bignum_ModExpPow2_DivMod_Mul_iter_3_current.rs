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
{
/* code modified by LLM (iteration 3): fixed reverse iteration issue */
let mut quotient = Vec::new();
    let mut remainder = Vec::new();

    for i in 0..dividend.len() {
        remainder.push(dividend[i]);

        let mut start = 0;
        while start < remainder.len() && remainder[start] == '0' {
            start += 1;
        }
        if start > 0 {
            remainder = remainder[start..].to_vec();
        }
        if remainder.is_empty() {
            remainder = vec!['0'];
        }

        let mut cmp = 0;
        if remainder.len() < divisor.len() {
            cmp = -1;
        } else if remainder.len() > divisor.len() {
            cmp = 1;
        } else {
            for j in 0..remainder.len() {
                if remainder[j] < divisor[j] {
                    cmp = -1;
                    break;
                } else if remainder[j] > divisor[j] {
                    cmp = 1;
                    break;
                }
            }
        }

        if cmp >= 0 {
            quotient.push('1');
            let padded_divisor = if remainder.len() > divisor.len() {
                let mut padded = vec!['0'; remainder.len() - divisor.len()];
                padded.extend(divisor);
                padded
            } else {
                divisor.to_vec()
            };
            let mut borrow = 0;
            let mut new_remainder = Vec::with_capacity(remainder.len());
            let len = remainder.len();
            for j in 0..len {
                let reverse_idx = len - 1 - j;
                let a_bit = remainder[reverse_idx];
                let b_bit = padded_divisor[reverse_idx];
                let a = if a_bit == '1' { 1 } else { 0 };
                let b = if b_bit == '1' { 1 } else { 0 };
                let diff = a - b - borrow;
                if diff < 0 {
                    borrow = 1;
                    new_remainder.push(if diff + 2 == 1 { '1' } else { '0' });
                } else {
                    borrow = 0;
                    new_remainder.push(if diff == 1 { '1' } else { '0' });
                }
            }
            new_remainder.reverse();
            let mut start = 0;
            while start < new_remainder.len() && new_remainder[start] == '0' {
                start += 1;
            }
            if start == new_remainder.len() {
                remainder = vec!['0'];
            } else {
                remainder = new_remainder[start..].to_vec();
            }
        } else {
            quotient.push('0');
        }
    }

    let mut start = 0;
    while start < quotient.len() && quotient[start] == '0' {
        start += 1;
    }
    if start == quotient.len() {
        quotient = vec!['0'];
    } else {
        quotient = quotient[start..].to_vec();
    }

    if remainder.is_empty() {
        remainder = vec!['0'];
    }

    (quotient, remainder)
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 2): fixed missing braces */
let mut result = vec!['0'];

    for i in 0..s2.len() {
        let j = s2.len() - 1 - i;
        if s2[j] == '1' {
            let mut shifted = s1.to_vec();
            shifted.extend(vec!['0'; i]);

            let a = &result;
            let b = &shifted;
            let mut carry = 0;
            let mut new_result = Vec::new();
            let mut idx_a = a.len() as isize - 1;
            let mut idx_b = b.len() as isize - 1;

            while idx_a >= 0 || idx_b >= 0 || carry > 0 {
                let bit_a = if idx_a >= 0 { a[idx_a as usize] } else { '0' };
                let bit_b = if idx_b >= 0 { b[idx_b as usize] } else { '0' };

                let x = if bit_a == '1' { 1 } else { 0 };
                let y = if bit_b == '1' { 1 } else { 0 };

                let sum = x + y + carry;
                carry = sum / 2;
                let bit = if sum % 2 == 1 { '1' } else { '0' };
                new_result.push(bit);

                if idx_a >= 0 { idx_a -= 1; }
                if idx_b >= 0 { idx_b -= 1; }
            }

            new_result.reverse();
            result = new_result;
        }
    }

    let mut start = 0;
    while start < result.len() && result[start] == '0' {
        start += 1;
    }
    if start == result.len() {
        result = vec!['0'];
    } else {
        result = result[start..].to_vec();
    }

    result
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
{
/* code modified by LLM (iteration 3): fixed int to usize conversion */
let mut is_zero = true;
    for i in 0..sy.len() {
        if sy[i] == '1' {
            is_zero = false;
            break;
        }
    }

    if is_zero {
        let one = vec!['1'];
        let (_, remainder) = DivMod(&one, sz);
        remainder
    } else {
        let mut result = sx.to_vec();
        for i in 0..n as usize {
            let squared = Mul(&result, &result);
            let (_, remainder) = DivMod(&squared, sz);
            result = remainder;
        }
        result
    }
}
// </vc-code>

fn main() {}
}
