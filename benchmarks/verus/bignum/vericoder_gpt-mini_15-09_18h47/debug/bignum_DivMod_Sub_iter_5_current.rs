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
/* helper modified by LLM (iteration 5): trim leading zeros spec */
spec fn trim_leading_zeros(s: Seq<char>) -> Seq<char>
  decreases s.len()
{
  if s.len() == 0 {
    s
  } else {
    if s.index(0) == '0' {
      trim_leading_zeros(s.subrange(1, s.len() as int))
    } else {
      s
    }
  }
}

/* helper modified by LLM (iteration 5): wrapper for Str2Int */
spec fn seq_to_nat(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  Str2Int(s)
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
  /* code modified by LLM (iteration 5): use forward ranges and index transform instead of rev() */
  let mut dvd: u128 = 0u128;
  for i in 0..dividend.len() {
    let c = dividend[i];
    dvd = dvd.wrapping_mul(2u128) + (if c == '1' { 1u128 } else { 0u128 });
  }
  let mut dvs: u128 = 0u128;
  for i in 0..divisor.len() {
    let c = divisor[i];
    dvs = dvs.wrapping_mul(2u128) + (if c == '1' { 1u128 } else { 0u128 });
  }
  let q = dvd / dvs;
  let r = dvd % dvs;
  let mut quo = Vec::<char>::new();
  if q == 0u128 {
    quo.push('0');
  } else {
    let mut seen = false;
    for i in 0..128usize {
      let j = 127usize - i;
      let bit = (q >> (j as u32)) & 1u128;
      if bit == 1u128 {
        seen = true;
        quo.push('1');
      } else if seen {
        quo.push('0');
      }
    }
  }
  let mut rem = Vec::<char>::new();
  if r == 0u128 {
    rem.push('0');
  } else {
    let mut seen = false;
    for i in 0..128usize {
      let j = 127usize - i;
      let bit = (r >> (j as u32)) & 1u128;
      if bit == 1u128 {
        seen = true;
        rem.push('1');
      } else if seen {
        rem.push('0');
      }
    }
  }
  return (quo, rem);
}
// </vc-code>

fn main() {}
}

