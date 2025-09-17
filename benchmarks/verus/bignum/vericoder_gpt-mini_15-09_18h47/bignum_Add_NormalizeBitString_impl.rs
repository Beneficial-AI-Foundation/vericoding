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
  // All characters must be '0' or '1'.
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@),
   t@.len() > 0,
   t@.len() > 1 ==> t@[0] != '0',
   ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): normalize bitstring by validating and stripping leading zeros */
  let mut k: int = 0;
  let mut first_one: Option<int> = Option::None;
  while k < s.len() as int
      invariant
          0 <= k && k <= s.len() as int,
      decreases
          s.len() as int - k
  {
      let c = s[k as usize];
      if c != '0' && c != '1' {
          let mut r = Vec::new();
          r.push('0');
          return r;
      }
      if c == '1' && first_one.is_none() {
          first_one = Option::Some(k);
      }
      k += 1;
  }
  if s.len() == 0 {
      let mut r = Vec::new();
      r.push('0');
      return r;
  }
  if first_one.is_none() {
      let mut r = Vec::new();
      r.push('0');
      return r;
  }
  let start = first_one.unwrap();
  let mut res = Vec::new();
  let mut p: int = start;
  while p < s.len() as int
      invariant
          start <= p && p <= s.len() as int,
      decreases
          s.len() as int - p
  {
      res.push(s[p as usize]);
      p += 1;
  }
  res
}
// </vc-code>

// <vc-helpers>
/* helper modified by LLM (iteration 3): simple helpers for bitstring validation and a lemma placeholder */

spec fn IsValidBitString(s: Seq<char>) -> bool {
  ValidBitString(s)
}

proof fn strip_leading_zeros_preserves_value(s: Seq<char>, t: Seq<char>)
  requires
    ValidBitString(s),
  ensures
    Str2Int(s) == Str2Int(t),
{
}

// </vc-helpers>

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@),
   ValidBitString(s2@),
  ensures ValidBitString(res@), 
    Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): binary addition with carries and normalization, using int-based measures for loops */
  let mut i: int = s1.len() as int;
  let mut j: int = s2.len() as int;
  let mut carry: int = 0;
  let mut rev: Vec<char> = Vec::new();
  while i > 0 || j > 0 || carry > 0
      invariant
          0 <= i && i <= s1.len() as int,
          0 <= j && j <= s2.len() as int,
          carry == 0 || carry == 1,
      decreases
          i + j + carry
  {
      let b1 = if i > 0 {
          if s1[(i - 1) as usize] == '1' { 1 } else { 0 }
      } else { 0 };
      let b2 = if j > 0 {
          if s2[(j - 1) as usize] == '1' { 1 } else { 0 }
      } else { 0 };
      let sum = b1 + b2 + carry;
      let bit = if sum % 2 == 1 { '1' } else { '0' };
      rev.push(bit);
      carry = if sum >= 2 { 1 } else { 0 };
      if i > 0 { i -= 1; }
      if j > 0 { j -= 1; }
  }
  let mut res: Vec<char> = Vec::new();
  let mut k: int = rev.len() as int;
  while k > 0
      invariant
          0 <= k && k <= rev.len() as int,
      decreases
          k
  {
      res.push(rev[(k - 1) as usize]);
      k -= 1;
  }
  // normalize: remove leading zeros but keep single '0' if all zeros
  let mut idx: int = 0;
  while idx < res.len() as int && res[idx as usize] == '0'
      invariant
          0 <= idx && idx <= res.len() as int,
      decreases
          res.len() as int - idx
  {
      idx += 1;
  }
  if idx == res.len() as int {
      let mut r = Vec::new();
      r.push('0');
      r
  } else if idx == 0 {
      res
  } else {
      let mut r = Vec::new();
      let mut p: int = idx;
      while p < res.len() as int
          invariant
              idx <= p && p <= res.len() as int,
          decreases
              res.len() as int - p
      {
          r.push(res[p as usize]);
          p += 1;
      }
      r
  }
}
// </vc-code>

fn main() {}
}


