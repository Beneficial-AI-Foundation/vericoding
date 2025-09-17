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
exec fn bits_val(v: &Vec<char>) -> u64 {
  let mut res = 0u64;
  let mut i = 0;
  while i < v.len() {
    if v[i] == '1' {
      res = res * 2 + 1;
    } else {
      res = res * 2;
    }
    i += 1;
  }
  res
}
exec fn nat_to_bits(n: u64) -> Vec<char> {
  if n == 0 {
    return Vec::new();
  }
  let mut v = Vec<char>::new();
  let mut remaining = n;
  while remaining > 0 {
    v.push(if remaining % 2 == 1 { '1' } else { '0' });
    remaining /= 2;
  }
  v.reverse();
  v
}
// </vc-helpers>

// <vc-spec>
exec fn DivMod_Sub(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
  let divisor_vec = Vec::from(divisor);
  let div_val = bits_val(&divisor_vec);
  let dividend_vec = Vec::from(dividend);
  let dividend_len = dividend.len();
  let mut numerical_r = 0u64;
  let mut quotient_vec = Vec::<char>::new();
  let mut i = 0;
  while i < dividend_len {
    let current_bit = if dividend_vec[i] == '1' { 1u64 } else { 0u64 };
    numerical_r = numerical_r * 2 + current_bit;
    if numerical_r >= div_val {
      numerical_r = numerical_r - div_val;
      quotient_vec.push('1');
    } else {
      quotient_vec.push('0');
    }
    i += 1;
  }
  let remainder_vec = nat_to_bits(numerical_r);
  (quotient_vec, remainder_vec)
}
// </vc-code>

fn main() {}
}

