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

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed compilation error by using Committee's nat for indexing */
exec fn CompareBitStrings(s1: &Seq<char>, s2: &Seq<char>) -> i32
    requires
        ValidBitString(*s1),
        ValidBitString(*s2),
    ensures
        CompareBitStrings(s1, s2) == -1 ==> Str2Int(*s1) < Str2Int(*s2),
        CompareBitStrings(s1, s2) == 0 ==> Str2Int(*s1) == Str2Int(*s2),
        CompareBitStrings(s1, s2) == 1 ==> Str2Int(*s1) > Str2Int(*s2),
    decreases
        s1.len() + s2.len()
{
    if s1.is_empty() {
        if s2.is_empty() {
            0
        } else {
            if s2.index(0) == '0' { 0 } else { -1 }
        }
    } else if s2.is_empty() {
        if s1.index(0) == '0' { 0 } else { 1 }
    } else {
        let sub1 = s1.subrange(0, s1.len() - 1 as nat);
        let sub2 = s2.subrange(0, s2.len() - 1 as nat);
        let sub_res = CompareBitStrings(&sub1, &sub2);
        if sub_res != 0 {
            sub_res
        } else {
            let last1 = s1.index(s1.len() - 1 as nat);
            let last2 = s2.index(s2.len() - 1 as nat);
            if last1 == last2 {
                0
            } else if last1 == '0' {
                -1
            } else {
                1
            }
        }
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
    /* code modified by LLM (iteration 2): implemented executable comparison using loops instead of recursion */
    let len1 = s1.len();
    let len2 = s2.len();
    let mut i = 0;
    while i < len1.min(len2) {
        if s1[i] != s2[i] {
            if s1[i] == '1' {
                return 1;
            } else {
                return -1;
            }
        }
        i = i + 1;
    }
    if len1 == len2 {
        return 0;
    } else if len1 > len2 {
        while i < len1 {
            if s1[i] == '1' {
                return 1;
            }
            i = i + 1;
        }
        return 0;
    } else {
        while i < len2 {
            if s2[i] == '1' {
                return -1;
            }
            i = i + 1;
        }
        return 0;
    }
}
// </vc-code>

fn main() {}
}


