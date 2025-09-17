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
  /* code modified by LLM (iteration 2): normalize by copying input and stripping leading zeros */
  let mut t: Vec<char> = Vec::new();
  let mut idx: usize = 0;
  while idx < s.len()
      invariant
          0 <= idx as int && idx as int <= s.len() as int,
      decreases s.len() as int - idx as int
  {
      t.push(s[idx]);
      idx += 1;
  }
  if t.len() == 0 {
      t.push('0');
  } else {
      while t.len() > 1 && t[0] == '0'
          invariant
              1 <= t.len() as int,
          decreases t.len() as int
      {
          t.remove(0);
      }
  }
  t
}
// </vc-code>

// <vc-spec>
exec fn CompareUnequal(s1: &[char], s2: &[char]) -> (res: i32)
  requires ValidBitString(s1@),
   ValidBitString(s2@),
   s1@.len() > 0,
   (s1@.len() > 1 ==> s1@[0] != '0'),
   s2@.len() > 0,
   (s2@.len() > 1 ==> s2@[0] != '0'),
   s1@.len() > s2@.len(),
  ensures Str2Int(s1@) < Str2Int(s2@) ==> res == -1,
    Str2Int(s1@) == Str2Int(s2@) ==> res == 0,
    Str2Int(s1@) > Str2Int(s2@) ==> res == 1
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): given the precondition that s1 is longer than s2 and both are normalized, s1 represents a larger integer */
  1
}
// </vc-code>

// <vc-helpers>
/* helper modified by LLM (iteration 2): lemma about Str2Int for a non-empty subrange */
proof fn Str2Int_subrange_last(s: Seq<char>, i: int)
    requires
        ValidBitString(s),
        0 <= i && i < s.len(),
    ensures
        Str2Int(s.subrange(0, i+1)) == 2 * Str2Int(s.subrange(0, i)) + (if s.index(i) == '1' { 1nat } else { 0nat }),
{
    assert(Str2Int(s.subrange(0, i+1)) == 2 * Str2Int(s.subrange(0, i)) + (if s.index(i) == '1' { 1nat } else { 0nat }));
}

/* helper modified by LLM (iteration 2): lemma that Str2Int of the empty sequence is zero */
proof fn Str2Int_empty()
    ensures
        Str2Int(Seq::<char>::empty()) == 0nat,
{
    assert(Str2Int(Seq::<char>::empty()) == 0nat);
}

// </vc-helpers>

// <vc-spec>
exec fn Compare(s1: &[char], s2: &[char]) -> (res: i32)
  requires ValidBitString(s1@),
   ValidBitString(s2@),
  ensures Str2Int(s1@) < Str2Int(s2@) ==> res == -1,
    Str2Int(s1@) == Str2Int(s2@) ==> res == 0,
    Str2Int(s1@) > Str2Int(s2@) ==> res == 1,
  decreases Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): normalize inputs then compare by length and lexicographically; use CompareUnequal for differing lengths */
  let t1 = NormalizeBitString(s1);
  let t2 = NormalizeBitString(s2);
  if t1.len() > t2.len() {
      CompareUnequal(&t1[..], &t2[..])
  } else if t1.len() < t2.len() {
      -CompareUnequal(&t2[..], &t1[..])
  } else {
      let mut i: usize = 0;
      while i < t1.len()
          invariant
              0 <= i as int && i as int <= t1.len() as int,
          decreases t1.len() as int - i as int
      {
          if t1[i] < t2[i] {
              return -1;
          } else if t1[i] > t2[i] {
              return 1;
          }
          i += 1;
      }
      0
  }
}
// </vc-code>

fn main() {}
}


