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
/* helper modified by LLM (iteration 7): trim leading zeros spec */
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

/* helper modified by LLM (iteration 7): wrapper for Str2Int */
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
  /* code modified by LLM (iteration 7): compute quotient and remainder using tracked ghost naturals and convert to bit vectors */
  let tracked mut i: int = 0;
  let tracked mut dvd_nat: nat = 0;
  while i < dividend.len() as int
      invariant
          0 <= i && i <= dividend.len() as int,
          dvd_nat == Str2Int(dividend@.subrange(0, i)),
      decreases dividend.len() as int - i
  {
    let c = dividend[i as usize];
    if c == '1' {
      dvd_nat = 2 * dvd_nat + 1;
    } else {
      dvd_nat = 2 * dvd_nat;
    }
    i += 1;
  }

  let tracked mut j: int = 0;
  let tracked mut dvs_nat: nat = 0;
  while j < divisor.len() as int
      invariant
          0 <= j && j <= divisor.len() as int,
          dvs_nat == Str2Int(divisor@.subrange(0, j)),
      decreases divisor.len() as int - j
  {
    let c = divisor[j as usize];
    if c == '1' {
      dvs_nat = 2 * dvs_nat + 1;
    } else {
      dvs_nat = 2 * dvs_nat;
    }
    j += 1;
  }

  let tracked q_nat: nat = dvd_nat / dvs_nat;
  let tracked r_nat: nat = dvd_nat % dvs_nat;

  let mut quo_rev: Vec<char> = Vec::new();
  if q_nat == 0 {
    quo_rev.push('0');
  } else {
    let tracked mut t: nat = q_nat;
    while t > 0
        invariant
            t >= 0,
        decreases t
    {
      let bit = if t % 2 == 1 { '1' } else { '0' };
      quo_rev.push(bit);
      t = t / 2;
    }
  }

  let mut quo: Vec<char> = Vec::new();
  let tracked mut k: int = quo_rev.len() as int;
  while k > 0
      invariant
          0 <= k && k <= quo_rev.len() as int,
      decreases k
  {
    k -= 1;
    quo.push(quo_rev[k as usize]);
  }

  let mut rem_rev: Vec<char> = Vec::new();
  if r_nat == 0 {
    rem_rev.push('0');
  } else {
    let tracked mut t: nat = r_nat;
    while t > 0
        invariant
            t >= 0,
        decreases t
    {
      let bit = if t % 2 == 1 { '1' } else { '0' };
      rem_rev.push(bit);
      t = t / 2;
    }
  }

  let mut rem: Vec<char> = Vec::new();
  let tracked mut kk: int = rem_rev.len() as int;
  while kk > 0
      invariant
          0 <= kk && kk <= rem_rev.len() as int,
      decreases kk
  {
    kk -= 1;
    rem.push(rem_rev[kk as usize]);
  }

  (quo, rem)
}
// </vc-code>

fn main() {}
}

