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
/* helper modified by LLM (iteration 9): relate sequence bits to natural value */
spec fn seq_to_nat(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 { 0 } else { 2 * seq_to_nat(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1 } else { 0 }) }
}

proof fn seq_to_nat_eq_Str2Int(s: Seq<char>)
    requires
        ValidBitString(s),
    ensures
        seq_to_nat(s) == Str2Int(s),
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        seq_to_nat_eq_Str2Int(s.subrange(0, s.len() as int - 1));
    }
}

// </vc-helpers>

// <vc-spec>
exec fn Sub(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@), Str2Int(s1@) >= Str2Int(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) - Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 9): compute numeric values then subtract and convert to binary */
  let mut p: usize = 0;
  let mut n1: nat = 0;
  while p < s1.len()
      invariant
          p <= s1.len(),
          n1 == seq_to_nat(s1@.subrange(0, p as int)),
      decreases s1.len() - p
  {
      n1 = 2 * n1 + if s1[p] == '1' { 1 } else { 0 };
      p += 1;
  }

  let mut q: usize = 0;
  let mut n2: nat = 0;
  while q < s2.len()
      invariant
          q <= s2.len(),
          n2 == seq_to_nat(s2@.subrange(0, q as int)),
      decreases s2.len() - q
  {
      n2 = 2 * n2 + if s2[q] == '1' { 1 } else { 0 };
      q += 1;
  }

  let mut diff: nat = n1 - n2;

  let mut rev = Vec::<char>::new();
  if diff == 0 {
      rev.push('0');
  } else {
      while diff > 0
          invariant
              rev.len() <= s1.len() + 1,
          decreases diff
      {
          if diff % 2 == 1 { rev.push('1'); } else { rev.push('0'); }
          diff = diff / 2;
      }
  }

  let mut out = Vec::<char>::new();
  while rev.len() > 0
      invariant
          rev.len() <= s1.len() + 1,
      decreases rev.len()
  {
      let ch = rev[rev.len() - 1];
      out.push(ch);
      rev.pop();
  }

  while out.len() > 1 && out[0] == '0'
      invariant
          out.len() >= 1,
      decreases out.len()
  {
      let mut tmp = Vec::<char>::new();
      let mut k: usize = 1;
      while k < out.len()
          invariant
              k <= out.len(),
              tmp.len() <= out.len() - 1,
          decreases out.len() - k
      {
          tmp.push(out[k]);
          k += 1;
      }
      out = tmp;
  }

  proof {
      seq_to_nat_eq_Str2Int(s1@);
      seq_to_nat_eq_Str2Int(s2@);
      assert(true);
  }

  out
}

// </vc-code>

fn main() {}
}


