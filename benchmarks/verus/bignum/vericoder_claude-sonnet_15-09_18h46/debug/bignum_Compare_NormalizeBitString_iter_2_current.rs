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
/* helper modified by LLM (iteration 2): added decreases clause */
proof fn str2int_monotonic(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() == s2.len(),
        exists |i: int| 0 <= i < s1.len() && s1.index(i) != s2.index(i) && forall |j: int| i < j < s1.len() ==> s1.index(j) == s2.index(j)
    ensures
        (exists |i: int| 0 <= i < s1.len() && s1.index(i) == '0' && s2.index(i) == '1' && forall |j: int| i < j < s1.len() ==> s1.index(j) == s2.index(j)) ==> Str2Int(s1) < Str2Int(s2)
    decreases s1.len()
{
}

proof fn str2int_length_property(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() < s2.len(),
        s2.len() > 0
    ensures
        Str2Int(s1) < Str2Int(s2)
    decreases s2.len()
{
}

proof fn str2int_equal_iff_seq_equal(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2)
    ensures
        Str2Int(s1) == Str2Int(s2) <==> s1 == s2
    decreases s1.len() + s2.len()
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
/* code modified by LLM (iteration 2): added decreases clause to while loop */
{
    if s1.len() != s2.len() {
        if s1.len() < s2.len() {
            proof {
                str2int_length_property(s1@, s2@);
            }
            return -1;
        } else {
            proof {
                str2int_length_property(s2@, s1@);
            }
            return 1;
        }
    }
    
    let mut i = 0;
    while i < s1.len()
        invariant
            i <= s1.len(),
            s1.len() == s2.len(),
            ValidBitString(s1@),
            ValidBitString(s2@),
            forall |j: int| 0 <= j < i ==> s1@.index(j) == s2@.index(j),
        decreases s1.len() - i
    {
        if s1[i] != s2[i] {
            if s1[i] == '0' && s2[i] == '1' {
                proof {
                    str2int_monotonic(s1@, s2@);
                }
                return -1;
            } else {
                proof {
                    str2int_monotonic(s2@, s1@);
                }
                return 1;
            }
        }
        i += 1;
    }
    
    proof {
        str2int_equal_iff_seq_equal(s1@, s2@);
    }
    return 0;
}
// </vc-code>

fn main() {}
}


