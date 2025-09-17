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
spec fn is_prefix_of(a: Seq<char>, b: Seq<char>) -> bool {
    exists |i: int| 0 <= i && a.len() + i <= b.len() && b.subrange(i, a.len() + i) == a
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
    let s1_seq = s1@;
    let s2_seq = s2@;

    if s1_seq.len() < s2_seq.len() {
        if Str2Int(s1_seq) == Str2Int(s2_seq.subrange(0, s1_seq.len() as int)) {
            -1
        } else if Str2Int(s1_seq) < Str2Int(s2_seq.subrange(0, s1_seq.len() as int)) {
            -1
        } else {
            1
        }
    } else if s1_seq.len() > s2_seq.len() {
        if Str2Int(s2_seq) == Str2Int(s1_seq.subrange(0, s2_seq.len() as int)) {
            1
        } else if Str2Int(s1_seq.subrange(0, s2_seq.len() as int)) < Str2Int(s2_seq) {
            -1
        } else {
            1
        }
    } else {
        if Str2Int(s1_seq) < Str2Int(s2_seq) {
            -1
        } else if Str2Int(s1_seq) == Str2Int(s2_seq) {
            0
        } else {
            1
        }
    }
}
// </vc-code>

fn main() {}
}


