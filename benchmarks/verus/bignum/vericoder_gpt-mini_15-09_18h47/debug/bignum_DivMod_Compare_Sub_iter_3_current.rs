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
/* helper modified by LLM (iteration 3): added pow2 and rem_to_bits spec functions */
spec fn pow2(k: int) -> nat
    requires
        k >= 0,
    decreases k
{
    if k == 0 {
        1
    } else {
        2 * pow2(k - 1)
    }
}

spec fn rem_to_bits(orig: nat, k: int) -> (res: Seq<char>)
    requires
        0 <= k,
        orig < pow2(k),
    ensures
        Str2Int(res) == orig,
        ValidBitString(res),
        res.len() == k as nat,
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
    /* code modified by LLM (iteration 3): compute quotient and remainder via integer simulation */
    let n = dividend.len();
    // compute numeric value of divisor (may overflow for very long inputs)
    let mut d_val: u128 = 0;
    for i in 0..divisor.len() {
        d_val = d_val * 2 + if divisor[i] == '1' { 1 } else { 0 };
    }
    let mut q: Vec<char> = Vec::new();
    let mut rem_val: u128 = 0;
    for i in 0..n {
        rem_val = rem_val * 2 + if dividend[i] == '1' { 1 } else { 0 };
        if rem_val >= d_val {
            q.push('1');
            rem_val = rem_val - d_val;
        } else {
            q.push('0');
        }
    }
    let k = divisor.len();
    let mut r: Vec<char> = Vec::new();
    for j in 0..k {
        let shift = (k - 1 - j) as u32;
        let bit = if (rem_val & ((1u128) << shift)) != 0 { '1' } else { '0' };
        r.push(bit);
    }
    (q, r)
}
// </vc-code>

fn main() {}
}

