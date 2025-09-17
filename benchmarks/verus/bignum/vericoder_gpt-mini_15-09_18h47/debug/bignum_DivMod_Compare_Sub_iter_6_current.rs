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
/* helper modified by LLM (iteration 6): pow2 as nat to ensure termination */
spec fn pow2(k: nat) -> nat
  decreases k
{
  if k == 0 {
    1
  } else {
    2 * pow2(k - 1)
  }
}

/* helper modified by LLM (iteration 6): rem_to_bits using nat k and requires orig < pow2(k) */
spec fn rem_to_bits(orig: nat, k: nat) -> Seq<char>
  requires orig < pow2(k)
  decreases k
{
  if k == 0 {
    Seq::empty()
  } else {
    let rest = rem_to_bits(orig / 2, k - 1);
    let bit = if orig % 2 == 1 { '1' } else { '0' };
    rest + seq![bit]
  }
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
    /* code modified by LLM (iteration 6): compute quotient and remainder using usize arithmetic and slice indexing */
    let n = dividend.len();
    let mut d_val: usize = 0;
    for i in 0..divisor.len() {
        let b = if divisor[i] == '1' { 1 } else { 0 };
        d_val = d_val * 2 + b;
    }
    let mut q: Vec<char> = Vec::new();
    let mut rem_val: usize = 0;
    for i in 0..n {
        let b = if dividend[i] == '1' { 1 } else { 0 };
        rem_val = rem_val * 2 + b;
        if rem_val >= d_val {
            q.push('1');
            rem_val = rem_val - d_val;
        } else {
            q.push('0');
        }
    }
    let k = divisor.len();
    let mut pow_vec: Vec<usize> = Vec::new();
    let mut p: usize = 1;
    for _ in 0..k {
        pow_vec.push(p);
        p = p * 2;
    }
    let mut r: Vec<char> = Vec::new();
    for j in 0..k {
        let idx = k - 1 - j;
        let denom = pow_vec[idx];
        if rem_val >= denom {
            r.push('1');
            rem_val = rem_val - denom;
        } else {
            r.push('0');
        }
    }
    (q, r)
}
// </vc-code>

fn main() {}
}

