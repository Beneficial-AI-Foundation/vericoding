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
        let sub1 = s1.subrange(0, s1.len() as int - 1);
        let sub2 = s2.subrange(0, s2.len() as int - 1);
        let sub_res = CompareBitStrings(&sub1, &sub2);
        if sub_res != 0 {
            sub_res
        } else {
            let last1 = s1.index(s1.len() as int - 1);
            let last2 = s2.index(s2.len() as int - 1);
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
    CompareBitStrings(&s1@, &s2@)
}
// </vc-code>

fn main() {}
}


