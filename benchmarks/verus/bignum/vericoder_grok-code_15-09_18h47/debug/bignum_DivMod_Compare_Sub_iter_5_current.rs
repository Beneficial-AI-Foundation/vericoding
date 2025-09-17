use vstd::prelude::*;

verus! {

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else {
    2 * Str2Int(s.subrange(0, s.len() as int - 1))
      + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
  }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
exec fn pad_front(vec: &[char], target_len: usize) -> (res: Vec<char>)
{
    let mut result = Vec::new();
    for _ in 0..(target_len - vec.len()) {
        result.push('0');
    }
    for c in vec.iter() {
        result.push(*c);
    }
    result
}

exec fn compare_pad(a: &[char], b: &[char]) -> (res: bool)
{
    let max_len = a.len().max(b.len());
    let a_pad = pad_front(a, max_len);
    let b_pad = pad_front(b, max_len);
    let mut i: usize = 0;
    while i < max_len {
        if a_pad[i] != b_pad[i] {
            return a_pad[i] > b_pad[i];
        }
        i += 1;
    }
    true
}

/* helper modified by LLM (iteration 3): Fixed compilation error with Vec::from by using Vec::new() and push */
exec fn subtract_pad(a: &[char], b: &[char], target_len: usize) -> (res: Vec<char>)
{
    let a_pad = pad_front(a, target_len);
    let b_pad = pad_front(b, target_len);
    let mut result = Vec::new();
    for _ in 0..target_len {
        result.push('0');
    }
    let mut borrow = 0;
    let mut i = target_len - 1;
    while i >= 0
        invariant
            0 <= i && i < target_len,
        decreases i,
    {
        let a_char = a_pad[i];
        let b_char = b_pad[i];
        let a_digit = if a_char == '1' { 1 } else { 0 };
        let b_digit = if b_char == '1' { 1 } else { 0 };
        let diff = a_digit - b_digit - borrow;
        let mut digit = diff;
        if digit < 0 {
            digit += 2;
            borrow = 1;
        } else {
            borrow = 0;
        }
        result[i] = if digit == 1 { '1' } else { '0' };
        if i == 0 { break; } else { i -= 1; }
    }
    // trim leading zeros
    let mut start = 0;
    while start < result.len() && result[start] == '0' {
        start += 1;
    }
    if start == result.len() {
        let mut zero_vec = Vec::new();
        zero_vec.push('0');
        zero_vec
    } else {
        let mut trimmed = Vec::new();
        for k in start..result.len() {
            trimmed.push(result[k]);
        }
        trimmed
    }
}

/* helper modified by LLM (iteration 5): Added slice_to_vec helper to manually copy slice to Vec and avoid compilation error with to_vec */
exec fn slice_to_vec(s: &[char]) -> (res: Vec<char>)
{
    let mut v = Vec::new();
    for &c in s.iter() {
        v.push(c);
    }
    v
}
// </vc-helpers>

// <vc-spec>
exec fn DivMod_Compare_Sub(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Removed prohibited to_vec calls and replaced with manual copy using slice_to_vec helper */
    let dividend_vec = slice_to_vec(dividend);
    let divisor_vec = slice_to_vec(divisor);
    let mut remainder = Vec::new();
    let mut quotient = Vec::new();
    let mut idx = 0;
    while idx < dividend_vec.len()
        invariant
            0 <= idx && idx <= dividend_vec.len(),
            ValidBitString(dividend_vec@),
            ValidBitString(divisor_vec@),
        decreases dividend_vec.len() - idx,
    {
        remainder.push(dividend_vec[idx]);
        let r_len = remainder.len() as usize;
        let b_len = divisor_vec.len() as usize;
        let target_len = r_len.max(b_len);
        if r_len >= b_len && compare_pad(&remainder, &divisor_vec) {
            remainder = subtract_pad(&remainder, &divisor_vec, target_len);
            quotient.push('1');
        } else {
            quotient.push('0');
        }
        idx += 1;
    }
    // trim leading zeros from quotient
    let mut q_start = 0;
    while q_start < quotient.len() && quotient[q_start] == '0' {
        q_start += 1;
    }
    let final_quotient = if q_start == quotient.len() {
        let mut zero_vec = Vec::new();
        zero_vec.push('0');
        zero_vec
    } else {
        let mut trim_q = Vec::new();
        for k in q_start..quotient.len() {
            trim_q.push(quotient[k]);
        }
        trim_q
    };
    (final_quotient, remainder)
}
// </vc-code>

fn main() {}
}

