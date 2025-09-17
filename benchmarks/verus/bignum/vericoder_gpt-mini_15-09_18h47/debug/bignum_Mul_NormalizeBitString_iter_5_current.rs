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
/* helper modified by LLM (iteration 5): convert '0'/'1' to nat bits */
fn char_to_bit(c: char) -> nat { if c == '1' { 1nat } else { 0nat } }
// </vc-helpers>

// <vc-spec>
exec fn Mul_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): compute product and build normalized bit string using nat literals */
  let len1 = s1.len();
  let len2 = s2.len();

  let mut i: usize = 0;
  let mut a1: nat = 0nat;
  while i < len1
      invariant
          0 <= i as int && i as int <= s1@.len() as int,
          a1 == Str2Int(s1@.subrange(0, i as int)),
      decreases s1@.len() as int - i as int
  {
      let c = s1[i];
      let bit: nat = char_to_bit(c);
      a1 = (2nat * a1) + bit;
      i += 1;
  }

  let mut j: usize = 0;
  let mut a2: nat = 0nat;
  while j < len2
      invariant
          0 <= j as int && j as int <= s2@.len() as int,
          a2 == Str2Int(s2@.subrange(0, j as int)),
      decreases s2@.len() as int - j as int
  {
      let c = s2[j];
      let bit: nat = char_to_bit(c);
      a2 = (2nat * a2) + bit;
      j += 1;
  }

  let orig: nat = a1 * a2;
  let mut p: nat = orig;

  let mut pow: nat = 1nat;
  while pow <= p
      invariant
          pow >= 1nat,
      decreases p + 1nat - pow
  {
      pow = pow * 2nat;
  }

  let mut res = Vec::<char>::new();

  while pow > 1nat
      invariant
          ValidBitString(res@),
          p < pow,
          orig == p + Str2Int(res@) * pow,
      decreases pow
  {
      let curr = pow / 2nat;
      if p >= curr {
          res.push('1');
          p = p - curr;
      } else {
          res.push('0');
      }
      pow = curr;
  }

  proof {
      assert(pow == 1nat);
      assert(p < pow);
      assert(p == 0nat);
      assert(orig == p + Str2Int(res@) * pow);
      assert(orig == Str2Int(res@));
  }

  res
}

// </vc-code>

fn main() {}
}
