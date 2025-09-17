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
  /* code modified by LLM (iteration 2): use usize indices and produce a valid normalized bitstring */
  let mut all_valid: bool = true;
  let mut k: usize = 0;
  while k < s.len() {
    let c = s[k];
    if c != '0' && c != '1' {
      all_valid = false;
      break;
    }
    k += 1;
  }
  if !all_valid {
    let mut r = Vec::new();
    r.push('0');
    return r;
  }

  // find first '1'
  let mut first_one: Option<usize> = None;
  let mut i: usize = 0;
  while i < s.len() {
    if s[i] == '1' {
      first_one = Some(i);
      break;
    }
    i += 1;
  }
  if first_one.is_none() {
    let mut r = Vec::new();
    r.push('0');
    return r;
  }
  let start = first_one.unwrap();
  let mut res = Vec::new();
  let mut j: usize = start;
  while j < s.len() {
    res.push(s[j]);
    j += 1;
  }
  res
}

// </vc-code>

// <vc-helpers>
/* helper modified by LLM (iteration 2): spec helpers relating sequences and Str2Int */

spec fn SeqToNat(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  Str2Int(s)
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
  /* code modified by LLM (iteration 2): binary addition using usize indices and normalization */
  let mut i = s1.len();
  let mut j = s2.len();
  let mut carry: usize = 0;
  let mut rev: Vec<char> = Vec::new();
  while i > 0 || j > 0 || carry > 0 {
    let b1 = if i > 0 {
      let c = s1[i - 1];
      if c == '1' { 1 } else { 0 }
    } else { 0 };
    let b2 = if j > 0 {
      let c = s2[j - 1];
      if c == '1' { 1 } else { 0 }
    } else { 0 };
    let sum = b1 + b2 + carry;
    let bit = if sum % 2 == 1 { '1' } else { '0' };
    rev.push(bit);
    carry = if sum >= 2 { 1 } else { 0 };
    if i > 0 { i -= 1; }
    if j > 0 { j -= 1; }
  }
  // reverse rev into res
  let mut res: Vec<char> = Vec::new();
  let mut k = rev.len();
  while k > 0 {
    res.push(rev[k - 1]);
    k -= 1;
  }
  // normalize: remove leading zeros but keep single '0' if all zeros
  let mut idx: usize = 0;
  while idx < res.len() && res[idx] == '0' {
    idx += 1;
  }
  if idx == res.len() {
    let mut r = Vec::new();
    r.push('0');
    r
  } else if idx == 0 {
    res
  } else {
    let mut r = Vec::new();
    let mut p = idx;
    while p < res.len() {
      r.push(res[p]);
      p += 1;
    }
    r
  }
}

// </vc-code>

fn main() {}
}


