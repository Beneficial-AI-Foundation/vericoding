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
/* helper modified by LLM (iteration 4): replaced for-in-reverse with while-loop to fix compilation trait error */
exec fn nat_to_bits(n: u64) -> Vec<char> {
  if n == 0 {
    return Vec::<char>::new();
  }
  let mut k = n;
  let mut len = 0;
  while k > 0 {
    len += 1;
    k /= 2;
  }
  let mut v: Vec<char> = Vec::with_capacity(len);
  let mut i = len - 1;
  while i >= 0 {
    let bit = if (n & (1u64 << i)) != 0 { '1' } else { '0' };
    v.push(bit);
    i -= 1;
  }
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
  /* code modified by LLM (iteration 5): manual copying to avoid Vec::from compilation error */
  let divisor_vec = {
    let mut v = Vec::new();
    let mut i = 0;
    while i < divisor.len() {
      v.push(divisor[i]);
      i += 1;
    }
    v
  };
  let div_val = bits_val(&divisor_vec);
  let dividend_vec = {
    let mut v = Vec::new();
    let mut i = 0;
    while i < dividend.len() {
      v.push(dividend[i]);
      i += 1;
    }
    v
  };
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

