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
    let mut t = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            i >= 0,
            i <= s.len(),
            ValidBitString(t@),
            Str2Int(s@) == Str2Int(t@),
        decreases s.len() - i
    {
        if s[i] == '1' {
            t.push('1');
            i += 1;
            while i < s.len() {
                invariant
                    i >= 0,
                    i <= s.len(),
                    ValidBitString(t@),
                    Str2Int(s@) == Str2Int(t@),
                decreases s.len() - i
                {
                    t.push(s[i]);
                    i += 1;
                }
            }
        } else if s[i] == '0' {
            i += 1;
        } else {
            proof { assert(false); }
        }
    }
    if t.is_empty() {
        t.push('0');
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
    let len1 = s1.len();
    let len2 = s2.len();
    if len1 > len2 {
        return 1;
    } else if len1 < len2 {
        return -1;
    }
    let mut i = 0;
    while i < len1
        invariant
            i >= 0,
            i <= len1,
            forall |j: int| 0 <= j && j < i ==> s1@[j] == s2@[j],
            Str2Int(s1@.subrange(i, len1 as int)) == Str2Int(s2@.subrange(i, len2 as int)) ==> res == 0,
            Str2Int(s1@.subrange(i, len1 as int)) < Str2Int(s2@.subrange(i, len2 as int)) ==> res == -1,
            Str2Int(s1@.subrange(i, len1 as int)) > Str2Int(s2@.subrange(i, len2 as int)) ==> res == 1,
        decreases len1 - i
    {
        if s1[i] != s2[i] {
            if s1[i] == '1' {
                return 1;
            } else {
                return -1;
            }
        }
        i += 1;
    }
    0
}
// </vc-code>

// <vc-helpers>
proof fn str2int_monotonic(s1: Seq<char>, s2: Seq<char>)
    requires ValidBitString(s1), ValidBitString(s2), s1.len() > s2.len()
    ensures Str2Int(s1) > Str2Int(s2)
{
    if s2.len() == 0 {
        assert(Str2Int(s1) >= 1);
    } else {
        let s1_prefix = s1.subrange(0, s1.len() as int - 1);
        let s2_prefix = s2.subrange(0, s2.len() as int - 1);
        str2int_monotonic(s1_prefix, s2_prefix);
    }
}

proof fn str2int_prefix_lemma(s: Seq<char>, i: int)
    requires ValidBitString(s), 0 <= i && i <= s.len() as int
    ensures Str2Int(s.subrange(0, i)) <= Str2Int(s)
{
    if i < s.len() as int {
        let rest = s.subrange(i, s.len() as int);
        str2int_prefix_lemma(s, i + 1);
    }
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
    let t1 = NormalizeBitString(s1);
    let t2 = NormalizeBitString(s2);
    if t1@.len() > t2@.len() {
        return 1;
    } else if t1@.len() < t2@.len() {
        return -1;
    } else {
        CompareUnequal(&t1, &t2)
    }
}
// </vc-code>

fn main() {}
}


