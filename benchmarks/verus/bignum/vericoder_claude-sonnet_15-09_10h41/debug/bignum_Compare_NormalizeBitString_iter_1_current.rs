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
proof fn str2int_monotonic(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() == s2.len(),
        exists |i: int| 0 <= i < s1.len() && s1.index(i) != s2.index(i) && forall |j: int| i < j < s1.len() ==> s1.index(j) == s2.index(j) && s1.index(i) < s2.index(i),
    ensures
        Str2Int(s1) < Str2Int(s2),
{
}

proof fn str2int_equal(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1 == s2,
    ensures
        Str2Int(s1) == Str2Int(s2),
{
}

proof fn str2int_length_monotonic(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() < s2.len(),
        s2.index(0) == '1',
    ensures
        Str2Int(s1) < Str2Int(s2),
{
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
    if s1.len() < s2.len() {
        if s2.len() > 0 && s2[0] == '1' {
            proof {
                str2int_length_monotonic(s1@, s2@);
            }
            return -1;
        }
        return -1;
    } else if s1.len() > s2.len() {
        if s1.len() > 0 && s1[0] == '1' {
            return 1;
        }
        return 1;
    } else {
        let mut i = 0;
        while i < s1.len()
            invariant
                0 <= i <= s1.len(),
                s1.len() == s2.len(),
                forall |j: int| 0 <= j < i ==> s1@.index(j) == s2@.index(j),
        {
            if s1[i] < s2[i] {
                return -1;
            } else if s1[i] > s2[i] {
                return 1;
            }
            i += 1;
        }
        proof {
            str2int_equal(s1@, s2@);
        }
        return 0;
    }
}
// </vc-code>

fn main() {}
}


