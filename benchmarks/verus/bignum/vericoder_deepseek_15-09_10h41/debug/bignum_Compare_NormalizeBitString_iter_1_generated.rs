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
proof fn str2int_monotonic(s1: Seq<char>, s2: Seq<char>, i: int)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        0 <= i && i <= s1.len() as int && i <= s2.len() as int,
        forall |j: int| 0 <= j && j < i ==> s1@[j] == s2@[j],
    ensures
        Str2Int(s1.subrange(0, i)) == Str2Int(s2.subrange(0, i)),
    decreases i
{
    if i > 0 {
        str2int_monotonic(s1, s2, i - 1);
    }
}

proof fn str2int_prefix_lt(s1: Seq<char>, s2: Seq<char>, i: int)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        0 <= i && i < s1.len() as int && i < s2.len() as int,
        forall |j: int| 0 <= j && j < i ==> s1@[j] == s2@[j],
        s1@[i] == '0' && s2@[i] == '1',
    ensures
        Str2Int(s1) < Str2Int(s2),
    decreases s1.len() as int - i
{
    str2int_monotonic(s1, s2, i);
    if i < s1.len() as int - 1 && i < s2.len() as int - 1 {
        str2int_prefix_lt(s1, s2, i + 1);
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
    let mut i = 0;
    let len1 = s1.len() as usize;
    let len2 = s2.len() as usize;
    
    while i < len1 && i < len2
        invariant
            ValidBitString(s1@),
            ValidBitString(s2@),
            0 <= i as int <= s1.len() as int,
            0 <= i as int <= s2.len() as int,
            forall |j: int| 0 <= j && j < i as int ==> s1@[j] == s2@[j],
            Str2Int(s1.subrange(0, i as int)) == Str2Int(s2.subrange(0, i as int)),
        decreases (len1 - i) + (len2 - i)
    {
        let c1 = s1[i];
        let c2 = s2[i];
        
        if c1 == '0' && c2 == '1' {
            proof {
                str2int_prefix_lt(s1@, s2@, i as int);
            }
            return -1;
        } else if c1 == '1' && c2 == '0' {
            proof {
                str2int_prefix_lt(s2@, s1@, i as int);
            }
            return 1;
        }
        
        i += 1;
    }
    
    if len1 < len2 {
        return -1;
    } else if len1 > len2 {
        return 1;
    } else {
        return 0;
    }
}
// </vc-code>

fn main() {}
}


