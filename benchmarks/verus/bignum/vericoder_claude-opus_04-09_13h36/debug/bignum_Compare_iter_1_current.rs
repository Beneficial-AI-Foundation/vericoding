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
proof fn lemma_str2int_zero(s: Seq<char>)
    requires 
        ValidBitString(s),
        forall |i: int| 0 <= i && i < s.len() ==> s[i] == '0',
    ensures Str2Int(s) == 0
    decreases s.len()
{
    if s.len() == 0 {
        // Base case: empty string
    } else {
        // Recursive case
        let s_prefix = s.subrange(0, s.len() as int - 1);
        assert forall |i: int| 0 <= i && i < s_prefix.len() implies s_prefix[i] == '0' by {
            assert(s_prefix[i] == s[i]);
        }
        lemma_str2int_zero(s_prefix);
        assert(s[s.len() - 1] == '0');
    }
}

proof fn lemma_str2int_positive(s: Seq<char>)
    requires 
        ValidBitString(s),
        s.len() > 0,
        exists |i: int| 0 <= i && i < s.len() && s[i] == '1',
    ensures Str2Int(s) > 0
    decreases s.len()
{
    if s.len() == 1 {
        assert(s[0] == '1');
    } else {
        let s_prefix = s.subrange(0, s.len() as int - 1);
        if s[s.len() - 1] == '1' {
            // Last bit is 1, so result is positive
        } else {
            // Last bit is 0, check prefix
            assert(exists |i: int| 0 <= i && i < s_prefix.len() && s_prefix[i] == '1');
            lemma_str2int_positive(s_prefix);
        }
    }
}

proof fn lemma_compare_same_length(s1: Seq<char>, s2: Seq<char>, pos: int)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() == s2.len(),
        0 <= pos <= s1.len(),
        forall |i: int| 0 <= i && i < pos ==> s1[i] == s2[i],
    ensures
        pos == s1.len() ==> Str2Int(s1) == Str2Int(s2),
        pos < s1.len() && s1[pos] == '0' && s2[pos] == '1' ==> Str2Int(s1) < Str2Int(s2),
        pos < s1.len() && s1[pos] == '1' && s2[pos] == '0' ==> Str2Int(s1) > Str2Int(s2),
    decreases s1.len() - pos
{
    if pos == s1.len() {
        if s1.len() == 0 {
            // Both empty
        } else {
            let s1_prefix = s1.subrange(0, s1.len() as int - 1);
            let s2_prefix = s2.subrange(0, s2.len() as int - 1);
            assert forall |i: int| 0 <= i && i < s1_prefix.len() implies s1_prefix[i] == s2_prefix[i] by {
                assert(s1_prefix[i] == s1[i]);
                assert(s2_prefix[i] == s2[i]);
            }
            lemma_compare_same_length(s1_prefix, s2_prefix, s1_prefix.len() as int);
            assert(s1[s1.len() - 1] == s2[s2.len() - 1]);
        }
    } else if pos < s1.len() {
        if s1.len() == 1 {
            assert(pos == 0);
        } else {
            let s1_suffix = s1.subrange(pos as int, s1.len() as int);
            let s2_suffix = s2.subrange(pos as int, s2.len() as int);
            
            if s1[pos] == '0' && s2[pos] == '1' {
                // s1 has 0, s2 has 1 at position pos
                // The suffix starting from pos in s2 is >= the suffix in s1
                assert(ValidBitString(s2_suffix));
                assert(s2_suffix[0] == '1');
                lemma_str2int_positive(s2_suffix);
            } else if s1[pos] == '1' && s2[pos] == '0' {
                // s1 has 1, s2 has 0 at position pos
                assert(ValidBitString(s1_suffix));
                assert(s1_suffix[0] == '1');
                lemma_str2int_positive(s1_suffix);
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
    let len1 = s1.len();
    let len2 = s2.len();
    
    if len1 < len2 {
        // s2 is longer, check if it has any '1' bits
        let mut has_one = false;
        let mut i = 0;
        while i < len2
            invariant 
                0 <= i <= len2,
                has_one == exists |j: int| 0 <= j && j < i && s2@[j] == '1',
        {
            if s2[i] == '1' {
                has_one = true;
                assert(s2@[i as int] == '1');
            }
            i = i + 1;
        }
        
        if has_one {
            proof {
                lemma_str2int_positive(s2@);
            }
            return -1;
        } else {
            proof {
                lemma_str2int_zero(s2@);
                lemma_str2int_zero(s1@);
            }
            return 0;
        }
    } else if len1 > len2 {
        // s1 is longer, check if it has any '1' bits
        let mut has_one = false;
        let mut i = 0;
        while i < len1
            invariant 
                0 <= i <= len1,
                has_one == exists |j: int| 0 <= j && j < i && s1@[j] == '1',
        {
            if s1[i] == '1' {
                has_one = true;
                assert(s1@[i as int] == '1');
            }
            i = i + 1;
        }
        
        if has_one {
            proof {
                lemma_str2int_positive(s1@);
            }
            return 1;
        } else {
            proof {
                lemma_str2int_zero(s1@);
                lemma_str2int_zero(s2@);
            }
            return 0;
        }
    } else {
        // Same length, compare lexicographically
        let mut i = 0;
        while i < len1
            invariant
                0 <= i <= len1,
                len1 == len2,
                forall |j: int| 0 <= j && j < i ==> s1@[j] == s2@[j],
        {
            if s1[i] < s2[i] {
                proof {
                    lemma_compare_same_length(s1@, s2@, i as int);
                }
                return -1;
            } else if s1[i] > s2[i] {
                proof {
                    lemma_compare_same_length(s1@, s2@, i as int);
                }
                return 1;
            }
            i = i + 1;
        }
        
        proof {
            lemma_compare_same_length(s1@, s2@, len1 as int);
        }
        return 0;
    }
}
// </vc-code>

fn main() {}
}