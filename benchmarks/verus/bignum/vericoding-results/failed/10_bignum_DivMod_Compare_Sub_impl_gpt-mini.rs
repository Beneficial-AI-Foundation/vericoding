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
/* helper modified by LLM (iteration 10): pow2 computes 2^k for integer k >= 0 */
spec fn pow2(k: int) -> nat
  requires
    k >= 0,
  decreases k
{
  if k == 0 {
    1nat
  } else {
    2 * pow2(k - 1)
  }
}

/* helper modified by LLM (iteration 10): rem_to_bits converts a nat into a k-length bit sequence (MSB-first) */
spec fn rem_to_bits(orig: nat, k: int) -> Seq<char>
  requires
    k >= 0,
  decreases k
{
  if k == 0 {
    Seq::empty()
  } else {
    let rest = rem_to_bits(orig / 2, k - 1);
    let bit = if orig % 2 == 1nat { '1' } else { '0' };
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
  /* code modified by LLM (iteration 10): safe nat arithmetic and int-indexed loops with invariants relating to Str2Int */
  let n: int = dividend.len() as int;
  let k: int = divisor.len() as int;

  if n == 0 {
    // quotient is 0, remainder is represented as k bits (possibly all '0')
    let mut r_empty: Vec<char> = Vec::new();
    r_empty.reserve(k as usize);
    let mut j: int = 0;
    while j < k
        invariant
            0 <= j && j <= k,
        decreases k - j
    {
      r_empty.push('0');
      j = j + 1;
    }
    return (Vec::<char>::new(), r_empty);
  }

  // compute divisor numeric value d_val = Str2Int(divisor@)
  let mut d_val: nat = 0;
  let mut i: int = 0;
  while i < k
      invariant
          0 <= i && i <= k,
          d_val == Str2Int(divisor@.subrange(0, i)),
      decreases k - i
  {
    let ch = divisor.index(i);
    let b: nat = if ch == '1' { 1 } else { 0 };
    d_val = d_val * 2 + b;
    i = i + 1;
  }

  // compute quotient numeric value q_val and remainder rem_val by long division
  let mut q_val: nat = 0;
  let mut rem_val: nat = 0;
  i = 0;
  while i < n
      invariant
          0 <= i && i <= n,
          rem_val == Str2Int(dividend@.subrange(0, i)) % d_val,
          q_val == Str2Int(dividend@.subrange(0, i)) / d_val,
      decreases n - i
  {
    let ch = dividend.index(i);
    let b: nat = if ch == '1' { 1 } else { 0 };
    rem_val = rem_val * 2 + b;
    if rem_val >= d_val {
      q_val = q_val * 2 + 1;
      rem_val = rem_val - d_val;
    } else {
      q_val = q_val * 2 + 0;
    }
    i = i + 1;
  }

  // build quotient bit-vector (n bits, MSB-first) from q_val
  let mut q: Vec<char> = Vec::new();
  q.reserve(n as usize);
  let mut p: nat = pow2(n - 1);
  let mut j: int = 0;
  while j < n
      invariant
          0 <= j && j <= n,
      decreases n - j
  {
    if q_val >= p {
      q.push('1');
      q_val = q_val - p;
    } else {
      q.push('0');
    }
    // safe: p >= 1 while j < n
    p = p / 2;
    j = j + 1;
  }

  // build remainder bit-vector (k bits, MSB-first) from rem_val
  let mut r: Vec<char> = Vec::new();
  r.reserve(k as usize);
  let mut p2: nat = pow2(k - 1);
  let mut t: int = 0;
  while t < k
      invariant
          0 <= t && t <= k,
      decreases k - t
  {
    if rem_val >= p2 {
      r.push('1');
      rem_val = rem_val - p2;
    } else {
      r.push('0');
    }
    p2 = p2 / 2;
    t = t + 1;
  }

  (q, r)
}

// </vc-code>

fn main() {}
}

