
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
exec fn remove_leading_zeros(mut s: Vec<char>) -> (res: Vec<char>)
  ensures ValidBitString(res@)
{
  while s.len() > 1 && s[0] == '0' {
    s.remove(0);
  }
  if s.is_empty() {
    s.push('0');
  }
  s
}

exec fn compare(a: &Vec<char>, b: &Vec<char>) -> (res: bool)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures res == (Str2Int(a@) >= Str2Int(b@))
{
  if a.len() > b.len() {
    return true;
  } else if a.len() < b.len() {
    return false;
  } else {
    let mut i = 0;
    while i < a.len() {
      if a[i] > b[i] {
        return true;
      }
      if a[i] < b[i] {
        return false;
      }
      i += 1;
    }
    return true;
  }
}

exec fn subtract_binary(a: &Vec<char>, b: &Vec<char>) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@), Str2Int(a@) >= Str2Int(b@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(a@) - Str2Int(b@)
{
  let len_a = a.len();
  let len_b = b.len();
  let mut b_padded = Vec::with_capacity(len_a);
  for _ in 0..(len_a - len_b) {
    b_padded.push('0');
  }
  b_padded.extend(b.iter().cloned());
  let mut result_lsb = Vec::new();
  let mut borrow = 0;
  let mut i = 0;
  while i < len_a {
    let idx = len_a - 1 - i;
    let bit_a = (a[idx] as u8 - b'0') as i32;
    let bit_b = (b_padded[idx] as u8 - b'0') as i32;
    let diff = bit_a - bit_b - borrow;
    if diff >= 0 {
      result_lsb.push((diff as u8 + b'0') as char);
      borrow = 0;
    } else {
      result_lsb.push((diff + 2) as u8 + b'0' as char);
      borrow = 1;
    }
    i += 1;
  }
  let mut result: Vec<char> = result_lsb.into_iter().rev().collect();
  result = remove_leading_zeros(result);
  result
}
// </vc-helpers>

// <vc-spec>
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
  let mut quotient = Vec::<char>::new();
  let mut remainder = Vec::<char>::new();
  let mut i = 0;
  while i < dividend.len() {
    remainder.push(dividend[i]);
    if compare(&remainder, divisor) {
      let new_remainder = subtract_binary(&remainder, divisor);
      remainder = new_remainder;
      quotient.push('1');
    } else {
      quotient.push('0');
    }
    i += 1;
  }
  (quotient, remainder)
}
// </vc-code>

fn main() {}
}


