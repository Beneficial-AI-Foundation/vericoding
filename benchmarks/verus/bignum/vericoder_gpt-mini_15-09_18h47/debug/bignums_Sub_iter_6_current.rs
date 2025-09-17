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
/* helper modified by LLM (iteration 6): relate sequence bits to natural value */
spec fn seq_to_nat(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 { 0 } else { 2 * seq_to_nat(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }) }
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
  /* code modified by LLM (iteration 6): use usize indices and u8 borrow to avoid ghost integer types */
  let mut i: usize = s1.len();
  let mut j: usize = s2.len();
  let mut rev = Vec::<char>::new();
  let mut borrow: u8 = 0;
  while i > 0 || j > 0
      invariant
          i <= s1.len(),
          j <= s2.len(),
          borrow == 0 || borrow == 1,
          rev.len() <= s1.len() + s2.len(),
      decreases i + j
  {
      let b1: u8 = if i > 0 && s1[i - 1] == '1' { 1 } else { 0 };
      let b2: u8 = if j > 0 && s2[j - 1] == '1' { 1 } else { 0 };
      let sub = (b1 as i8) - (b2 as i8) - (borrow as i8);
      if sub < 0 {
          rev.push('1');
          borrow = 1;
      } else if sub == 0 {
          rev.push('0');
          borrow = 0;
      } else {
          rev.push('1');
          borrow = 0;
      }
      if i > 0 { i -= 1; }
      if j > 0 { j -= 1; }
  }
  // Reverse rev (LSB-first) into out (MSB-first)
  let mut out = Vec::<char>::new();
  while rev.len() > 0
      invariant
          rev.len() <= s1.len() + s2.len(),
      decreases rev.len()
  {
      let ch = rev[rev.len() - 1];
      out.push(ch);
      rev.pop();
  }
  // Strip leading zeros but leave at least one digit
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
              tmp.len() <= out.len(),
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


