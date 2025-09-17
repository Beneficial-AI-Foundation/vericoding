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
        exists |i: int| 0 <= i < s1.len() && s1[i] != s2[i] && (forall |j: int| i < j < s1.len() ==> s1[j] == s2[j]),
        s1[i] == '0',
        s2[i] == '1'
    ensures Str2Int(s1) < Str2Int(s2)
{
}

proof fn str2int_equal(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1 == s2
    ensures Str2Int(s1) == Str2Int(s2)
{
}

proof fn str2int_length_comparison(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() < s2.len(),
        s2.len() > 0
    ensures Str2Int(s1) < Str2Int(s2)
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
    let len1 = s1.len();
    let len2 = s2.len();
    
    if len1 < len2 {
        proof {
            str2int_length_comparison(s1@, s2@);
        }
        return -1;
    } else if len1 > len2 {
        proof {
            str2int_length_comparison(s2@, s1@);
        }
        return 1;
    } else {
        // Same length, compare lexicographically from left to right
        let mut i = 0;
        while i < len1
            invariant
                0 <= i <= len1,
                len1 == len2,
                ValidBitString(s1@),
                ValidBitString(s2@),
                forall |j: int| 0 <= j < i ==> s1@[j] == s2@[j]
        {
            if s1[i] < s2[i] {
                proof {
                    str2int_monotonic(s1@, s2@);
                }
                return -1;
            } else if s1[i] > s2[i] {
                proof {
                    str2int_monotonic(s2@, s1@);
                }
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


