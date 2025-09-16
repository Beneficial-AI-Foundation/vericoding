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
/* helper modified by LLM (iteration 10): trim leading zeros spec */
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

/* helper modified by LLM (iteration 10): wrapper for Str2Int */
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
  /* code modified by LLM (iteration 10): generate binary string Vec<char> for quotient and remainder, removed invalid nat suffixes */
  let tracked dvd_nat: nat = Str2Int(dividend@);
  let tracked dvs_nat: nat = Str2Int(divisor@);

  let tracked q_nat: nat = dvd_nat / dvs_nat;
  let tracked r_nat: nat = dvd_nat % dvs_nat;

  let mut quo_rev: Vec<char> = Vec::new();
  if q_nat == 0 {
    quo_rev.push('0');
  } else {
    let tracked mut t: nat = q_nat;
    while t > 0 {
      let bit = if t % 2 == 1 { '1' } else { '0' };
      quo_rev.push(bit);
      t = t / 2;
    }
  }

  let mut quo: Vec<char> = Vec::new();
  let mut idx: usize = quo_rev.len();
  while idx > 0 {
    idx -= 1;
    quo.push(quo_rev[idx]);
  }

  let mut rem_rev: Vec<char> = Vec::new();
  if r_nat == 0 {
    rem_rev.push('0');
  } else {
    let tracked mut t2: nat = r_nat;
    while t2 > 0 {
      let bit = if t2 % 2 == 1 { '1' } else { '0' };
      rem_rev.push(bit);
      t2 = t2 / 2;
    }
  }

  let mut rem: Vec<char> = Vec::new();
  let mut idx2: usize = rem_rev.len();
  while idx2 > 0 {
    idx2 -= 1;
    rem.push(rem_rev[idx2]);
  }

  (quo, rem)
}
// </vc-code>

fn main() {}
}

