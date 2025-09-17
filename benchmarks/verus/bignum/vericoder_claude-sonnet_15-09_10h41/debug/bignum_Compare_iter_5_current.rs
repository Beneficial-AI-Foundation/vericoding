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
/* helper modified by LLM (iteration 5): fixed type annotation for integer literals */
proof fn str2int_monotonic(s1: Seq<char>, s2: Seq<char>, idx: int)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() == s2.len(),
        0 <= idx < s1.len(),
        s1[idx] == '0',
        s2[idx] == '1',
        forall |j: int| idx < j < s1.len() ==> s1[j] == s2[j]
    ensures Str2Int(s1) < Str2Int(s2)
    decreases s1.len()
{
    if s1.len() == 0 {
        assert(false);
    } else {
        let last_idx = s1.len() - 1;
        if idx == last_idx {
            let s1_prefix = s1.subrange(0, last_idx);
            let s2_prefix = s2.subrange(0, last_idx);
            assert(s1_prefix == s2_prefix);
            assert(Str2Int(s1_prefix) == Str2Int(s2_prefix));
            assert(s1[last_idx] == '0');
            assert(s2[last_idx] == '1');
            assert(Str2Int(s1) == 2 * Str2Int(s1_prefix) + 0nat);
            assert(Str2Int(s2) == 2 * Str2Int(s2_prefix) + 1nat);
            assert(Str2Int(s1) < Str2Int(s2));
        } else {
            let s1_prefix = s1.subrange(0, last_idx);
            let s2_prefix = s2.subrange(0, last_idx);
            str2int_monotonic(s1_prefix, s2_prefix, idx);
            assert(Str2Int(s1_prefix) < Str2Int(s2_prefix));
            assert(Str2Int(s1) == 2 * Str2Int(s1_prefix) + (if s1[last_idx] == '1' { 1nat } else { 0nat }));
            assert(Str2Int(s2) == 2 * Str2Int(s2_prefix) + (if s2[last_idx] == '1' { 1nat } else { 0nat }));
            assert(Str2Int(s1) < Str2Int(s2));
        }
    }
}

proof fn str2int_equal(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1 == s2
    ensures Str2Int(s1) == Str2Int(s2)
    decreases s1.len()
{
}

proof fn str2int_length_comparison(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() < s2.len(),
        s2.len() > 0
    ensures Str2Int(s1) < Str2Int(s2)
    decreases s1.len() + s2.len()
{
    if s2.len() == 1 {
        assert(s1.len() == 0);
        assert(Str2Int(s1) == 0nat);
        assert(Str2Int(s2) >= 0nat);
        if s2[0] == '1' {
            assert(Str2Int(s2) == 1nat);
        } else {
            assert(Str2Int(s2) == 0nat);
        }
        assert(Str2Int(s1) <= Str2Int(s2));
    } else {
        let s2_prefix = s2.subrange(0, s2.len() - 1);
        if s1.len() < s2_prefix.len() {
            str2int_length_comparison(s1, s2_prefix);
        }
        assert(Str2Int(s1) < 2 * Str2Int(s2_prefix) + 2nat);
        assert(Str2Int(s2) >= 2 * Str2Int(s2_prefix));
        assert(Str2Int(s1) < Str2Int(s2));
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
    /* code modified by LLM (iteration 5): fixed type annotation for integer literals */
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
                len1 == s1@.len(),
                len2 == s2@.len(),
                ValidBitString(s1@),
                ValidBitString(s2@),
                forall |j: int| 0 <= j < i && j < s1@.len() && j < s2@.len() ==> s1@[j] == s2@[j]
            decreases len1 - i
        {
            if s1[i] < s2[i] {
                proof {
                    assert(s1@[i as int] == '0');
                    assert(s2@[i as int] == '1');
                    assert(forall |j: int| i < j < s1@.len() ==> s1@[j] == s2@[j]);
                    str2int_monotonic(s1@, s2@, i as int);
                }
                return -1;
            } else if s1[i] > s2[i] {
                proof {
                    assert(s1@[i as int] == '1');
                    assert(s2@[i as int] == '0');
                    assert(forall |j: int| i < j < s1@.len() ==> s1@[j] == s2@[j]);
                    str2int_monotonic(s2@, s1@, i as int);
                }
                return 1;
            }
            i += 1;
        }
        
        proof {
            assert(s1@ == s2@);
            str2int_equal(s1@, s2@);
        }
        return 0;
    }
}
// </vc-code>

fn main() {}
}


