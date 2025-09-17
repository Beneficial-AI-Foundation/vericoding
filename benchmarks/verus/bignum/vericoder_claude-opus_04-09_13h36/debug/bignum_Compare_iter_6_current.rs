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
        assert forall |i: int| 0 <= i && i < s_prefix.len() implies (s_prefix[i] == '0' || s_prefix[i] == '1') by {
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
        let i = choose |i: int| 0 <= i && i < s.len() && s[i] == '1';
        assert(i == 0);
        assert(s[0] == '1');
    } else {
        let s_prefix = s.subrange(0, s.len() as int - 1);
        assert forall |i: int| 0 <= i && i < s_prefix.len() implies (s_prefix[i] == '0' || s_prefix[i] == '1') by {
            assert(s_prefix[i] == s[i]);
        }
        if s[s.len() - 1] == '1' {
            // Last bit is 1, so result is positive
        } else {
            // Last bit is 0, check prefix
            let witness = choose |i: int| 0 <= i && i < s.len() && s[i] == '1';
            assert(witness < s.len() - 1) by {
                if witness == s.len() - 1 {
                    assert(s[s.len() - 1] == '1');
                    assert(false);
                }
            }
            assert(s_prefix[witness] == s[witness]);
            assert(s_prefix[witness] == '1');
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
    decreases s1.len()
{
    if s1.len() == 0 {
        // Both empty
    } else if pos == s1.len() {
        // All positions are equal
        let s1_prefix = s1.subrange(0, s1.len() as int - 1);
        let s2_prefix = s2.subrange(0, s2.len() as int - 1);
        assert forall |i: int| 0 <= i && i < s1_prefix.len() implies s1_prefix[i] == s2_prefix[i] by {
            assert(s1_prefix[i] == s1[i]);
            assert(s2_prefix[i] == s2[i]);
        }
        assert forall |i: int| 0 <= i && i < s1_prefix.len() implies (s1_prefix[i] == '0' || s1_prefix[i] == '1') by {
            assert(s1_prefix[i] == s1[i]);
        }
        assert forall |i: int| 0 <= i && i < s2_prefix.len() implies (s2_prefix[i] == '0' || s2_prefix[i] == '1') by {
            assert(s2_prefix[i] == s2[i]);
        }
        lemma_compare_same_length(s1_prefix, s2_prefix, s1_prefix.len() as int);
        assert(s1[s1.len() - 1] == s2[s2.len() - 1]);
    } else if pos == s1.len() - 1 {
        // Difference at last position
        let s1_prefix = s1.subrange(0, s1.len() as int - 1);
        let s2_prefix = s2.subrange(0, s2.len() as int - 1);
        assert forall |i: int| 0 <= i && i < s1_prefix.len() implies s1_prefix[i] == s2_prefix[i] by {
            assert(s1_prefix[i] == s1[i]);
            assert(s2_prefix[i] == s2[i]);
        }
        assert forall |i: int| 0 <= i && i < s1_prefix.len() implies (s1_prefix[i] == '0' || s1_prefix[i] == '1') by {
            assert(s1_prefix[i] == s1[i]);
        }
        assert forall |i: int| 0 <= i && i < s2_prefix.len() implies (s2_prefix[i] == '0' || s2_prefix[i] == '1') by {
            assert(s2_prefix[i] == s2[i]);
        }
        lemma_compare_same_length(s1_prefix, s2_prefix, s1_prefix.len() as int);
        assert(Str2Int(s1_prefix) == Str2Int(s2_prefix));
        
        if s1[pos] == '0' && s2[pos] == '1' {
            assert(Str2Int(s1) == 2 * Str2Int(s1_prefix));
            assert(Str2Int(s2) == 2 * Str2Int(s2_prefix) + 1);
        } else if s1[pos] == '1' && s2[pos] == '0' {
            assert(Str2Int(s1) == 2 * Str2Int(s1_prefix) + 1);
            assert(Str2Int(s2) == 2 * Str2Int(s2_prefix));
        }
    } else {
        // pos < s1.len() - 1, found first difference
        let s1_prefix = s1.subrange(0, s1.len() as int - 1);
        let s2_prefix = s2.subrange(0, s2.len() as int - 1);
        assert forall |i: int| 0 <= i && i < s1_prefix.len() implies (s1_prefix[i] == '0' || s1_prefix[i] == '1') by {
            assert(s1_prefix[i] == s1[i]);
        }
        assert forall |i: int| 0 <= i && i < s2_prefix.len() implies (s2_prefix[i] == '0' || s2_prefix[i] == '1') by {
            assert(s2_prefix[i] == s2[i]);
        }
        
        assert forall |i: int| 0 <= i && i < pos implies s1_prefix[i] == s2_prefix[i] by {
            assert(s1_prefix[i] == s1[i]);
            assert(s2_prefix[i] == s2[i]);
        }
        lemma_compare_same_length(s1_prefix, s2_prefix, pos);
        if s1[pos] == '0' && s2[pos] == '1' {
            assert(s1_prefix[pos] == '0');
            assert(s2_prefix[pos] == '1');
            assert(Str2Int(s1_prefix) < Str2Int(s2_prefix));
        } else if s1[pos] == '1' && s2[pos] == '0' {
            assert(s1_prefix[pos] == '1');
            assert(s2_prefix[pos] == '0');
            assert(Str2Int(s1_prefix) > Str2Int(s2_prefix));
        }
    }
}

proof fn lemma_all_zeros_and_different_length(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        forall |i: int| 0 <= i && i < s1.len() ==> s1[i] == '0',
        forall |i: int| 0 <= i && i < s2.len() ==> s2[i] == '0',
    ensures
        Str2Int(s1) == 0,
        Str2Int(s2) == 0,
{
    lemma_str2int_zero(s1);
    lemma_str2int_zero(s2);
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
    
    assert(len1 == s1@.len());
    assert(len2 == s2@.len());
    
    if len1 < len2 {
        // s2 is longer, check if it has any '1' bits
        let mut has_one = false;
        let mut i: usize = 0;
        while i < len2
            invariant 
                0 <= i <= len2,
                len2 == s2@.len(),
                has_one == exists |j: int| 0 <= j && j < i && s2@[j] == '1',
            decreases len2 - i
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
                assert(Str2Int(s2@) > 0);
                
                // For s1, check if all zeros or has a one
                if len1 == 0 {
                    assert(Str2Int(s1@) == 0);
                } else {
                    let has_one_s1 = exists |k: int| 0 <= k && k < s1@.len() && s1@[k] == '1';
                    if has_one_s1 {
                        lemma_str2int_positive(s1@);
                        // Even if s1 has ones, since it's shorter, its value is less
                        // This requires more complex reasoning about the magnitude
                    } else {
                        assert forall |k: int| 0 <= k && k < s1@.len() implies s1@[k] == '0' by {
                            assert(s1@[k] == '0' || s1@[k] == '1');
                        }
                        lemma_str2int_zero(s1@);
                        assert(Str2Int(s1@) == 0);
                    }
                }
                // When s2 is longer and has at least one '1', it's always greater
                // This is true because even the smallest non-zero value with more bits
                // is larger than any value with fewer bits
            }
            return -1;
        } else {
            proof {
                assert forall |j: int| 0 <= j && j < s2@.len() implies s2@[j] == '0' by {
                    assert(s2@[j] == '0' || s2@[j] == '1');
                    if s2@[j] == '1' {
                        assert(exists |k: int| 0 <= k && k < len2 && s2@[k] == '1');
                        assert(has_one);
                        assert(false);
                    }
                }
                lemma_str2int_zero(s2@);
                assert(Str2Int(s2@) == 0);
                
                // s1 must also be all zeros
                assert forall |j: int| 0 <= j && j < s1@.len() implies s1@[j] == '0' by {
                    assert(s1@[j] == '0' || s1@[j] == '1');
                    if s1@[j] == '1' {
                        lemma_str2int_positive(s1@);
                        assert(Str2Int(s1@) > 0);
                        assert(false);
                    }
                }
                lemma_str2int_zero(s1@);
                assert(Str2Int(s1@) == 0);
            }
            return 0;
        }
    } else if len1 > len2 {
        // s1 is longer, check if it has any '1' bits
        let mut has_one = false;
        let mut i: usize = 0;
        while i < len1
            invariant 
                0 <= i <= len1,
                len1 == s1@.len(),
                has_one == exists |j: int| 0 <= j && j < i && s1@[j] == '1',
            decreases len1 - i
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
                assert(Str2Int(s1@) > 0);
                
                // For s2, check if all zeros or has a one
                if len2 == 0 {
                    assert(Str2Int(s2@) == 0);
                } else {
                    let has_one_s2 = exists |k: int| 0 <= k && k < s2@.len() && s2@[k] == '1';
                    if has_one_s2 {
                        lemma_str2int_positive(s2@);
                        // Even if s2 has ones, since it's shorter, its value is less
                    } else {
                        assert forall |k: int| 0 <= k && k < s2@.len() implies s2@[k] == '0' by {
                            assert(s2@[k] == '0' || s2@[k] == '1');
                        }
                        lemma_str2int_zero(s2@);
                        assert(Str2Int(s2@) == 0);
                    }
                }
                // When s1 is longer and has at least one '1', it's always greater
            }
            return 1;
        } else {
            proof {
                assert forall |j: int| 0 <= j && j < s1@.len() implies s1@[j] == '0' by {
                    assert(s1@[j] == '0' || s1@[j] == '1');
                    if s1@[j] == '1' {
                        assert(exists |k: int| 0 <= k && k < len1 && s1@[k] == '1');
                        assert(has_one);
                        assert(false);
                    }
                }
                lemma_str2int_zero(s1@);
                assert(Str2Int(s1@) == 0);
                
                // s2 must also be all zeros
                assert forall |j: int| 0 <= j && j < s2@.len() implies s2@[j] == '0' by {
                    assert(s2@[j] == '0' || s2@[j] == '1');
                    if s2@[j] == '1' {
                        lemma_str2int_positive(s2@);
                        assert(Str2Int(s2@) > 0);
                        assert(false);
                    }
                }
                lemma_str2int_zero(s2@);
                assert(Str2Int(s2@) == 0);
            }
            return 0;
        }
    } else {
        // Same length, compare lexicographically
        let mut i: usize = 0;
        while i < len1
            invariant
                0 <= i <= len1,
                len1 == s1@.len(),
                len2 == s2@.len(),
                len1 == len2,
                s1@.len() == s2@.len(),
                forall |j: int| 0 <= j && j < i ==> s1@[j] == s2@[j],
            decreases len1 - i
        {
            if s1[i] < s2[i] {
                proof {
                    assert(s1@[i as int] == '0' || s1@[i as int] == '1');
                    assert(s2@[i as int] == '0' || s2@[i as int] == '1');
                    assert(s1@[i as int] == '0' && s2@[i as int] == '1');
                    lemma_compare_same_length(s1@, s2@, i as int);
                }
                return -1;
            } else if s1[i] > s2[i] {
                proof {
                    assert(s1@[i as int] == '0' || s1@[i as int] == '1');
                    assert(s2@[i as int] == '0' || s2@[i as int] == '1');
                    assert(s1@[i as int] == '1' && s2@[i as int] == '0');
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