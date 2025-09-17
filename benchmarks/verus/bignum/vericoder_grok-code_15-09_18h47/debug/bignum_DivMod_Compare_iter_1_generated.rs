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
exec fn remove_leading_zeros(v: &Vec<char>) -> Vec<char>
{
    let mut i: usize = 0;
    while i < v.len() {
        if v[i] == '1' {
            break;
        }
        i += 1;
    }
    let mut result = Vec::new();
    for j in i..v.len() {
        result.push(v[j]);
    }
    result
}

exec fn is_greater_or_equal(v1: &Vec<char>, v2: &Vec<char>) -> bool
{
    let l1 = v1.len();
    let l2 = v2.len();
    if l1 > l2 {
        return true;
    }
    if l1 < l2 {
        return false;
    }
    for i in 0..l1 {
        if v1[i] > v2[i] {
            return true;
        }
        if v1[i] < v2[i] {
            return false;
        }
    }
    true
}

exec fn subtract(v1: &Vec<char>, v2: &Vec<char>) -> Vec<char>
    requires is_greater_or_equal(v1, v2)
{
    let l1 = v1.len();
    let l2 = v2.len();
    let mut v2_padded = Vec::new();
    for _ in 0..(l1 - l2) {
        v2_padded.push('0');
    }
    v2_padded.extend(v2.iter().cloned());
    let mut result = Vec::new();
    let mut borrow = 0;
    for j in (0..l1).rev() {
        let d1 = v1[j] as i32 - '0' as i32;
        let d2 = v2_padded[j] as i32 - '0' as i32;
        let mut res = d1 - borrow - d2;
        if res < 0 {
            res += 2;
            borrow = 1;
        } else {
            borrow = 0;
        }
        result.push((res + '0' as i32) as u8 as char);
    }
    result.reverse();
    remove_leading_zeros(&result)
}
// </vc-helpers>

// <vc-spec>
exec fn DivMod_Compare(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
    let dividend_v = dividend.to_vec();
    let divisor_v = divisor.to_vec();
    let div_trimmed = remove_leading_zeros(&dividend_v);
    let divr_trimmed = remove_leading_zeros(&divisor_v);
    let mut remainder: Vec<char> = Vec::new();
    let mut quotient: Vec<char> = Vec::new();
    for &c in div_trimmed.iter() {
        remainder.push(c);
        if is_greater_or_equal(&remainder, &divr_trimmed) {
            quotient.push('1');
            remainder = subtract(&remainder, &divr_trimmed);
        } else {
            quotient.push('0');
        }
    }
    let mut quo_v = remove_leading_zeros(&quotient);
    if quo_v.is_empty() {
        quo_v = vec!['0'];
    }
    let mut rem_v = remove_leading_zeros(&remainder);
    if rem_v.is_empty() {
        rem_v = vec!['0'];
    }
    (quo_v, rem_v)
}
// </vc-code>

fn main() {}
}

