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
/* helper modified by LLM (iteration 2): bool-to-char conversion */
fn bit_of(b: bool) -> char { if b { '1' } else { '0' } }
// </vc-helpers>

// <vc-spec>
exec fn Mul_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): avoid casting slice lengths to int by using usize counters and int casts in invariants */
  let len1 = s1.len();
  let len2 = s2.len();

  // compute numeric value of s1
  let mut i: usize = 0;
  let mut a1: nat = 0;
  while i < len1
      invariant
          0 <= i as int && i as int <= s1@.len(),
          a1 == Str2Int(s1@.subrange(0, i as int)),
      decreases s1@.len() - i as int
  {
      let c = s1[i];
      let bit: nat = if c == '1' { 1 } else { 0 };
      a1 = 2 * a1 + bit;
      i += 1;
  }

  // compute numeric value of s2
  let mut j: usize = 0;
  let mut a2: nat = 0;
  while j < len2
      invariant
          0 <= j as int && j as int <= s2@.len(),
          a2 == Str2Int(s2@.subrange(0, j as int)),
      decreases s2@.len() - j as int
  {
      let c = s2[j];
      let bit: nat = if c == '1' { 1 } else { 0 };
      a2 = 2 * a2 + bit;
      j += 1;
  }

  let orig: nat = a1 * a2;
  let mut p: nat = orig;

  // find smallest power of two strictly greater than p
  let mut pow: nat = 1;
  while pow <= p
      invariant
          pow >= 1,
      decreases p + 1 - pow
  {
      pow = pow * 2;
  }

  let mut res = Vec::<char>::new();

  // build bits most-significant-first
  while pow > 1
      invariant
          ValidBitString(res@),
          0 <= p && p < pow,
          orig == p + Str2Int(res@) * pow,
      decreases pow
  {
      let curr = pow / 2;
      if p >= curr {
          res.push('1');
          p = p - curr;
      } else {
          res.push('0');
      }
      pow = curr;
  }

  proof {
      // at termination pow == 1 and 0 <= p < pow implies p == 0
      assert(pow == 1);
      assert(p == 0);
      assert(Str2Int(res@) == orig);
  }

  res
}
// </vc-code>

fn main() {}
}
