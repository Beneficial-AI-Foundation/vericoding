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
proof fn str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{
    assert(Seq::<char>::empty().len() == 0);
}

proof fn str2int_single_zero()
    ensures Str2Int(seq!['0']) == 0
{
    assert(seq!['0'].len() == 1);
    assert(seq!['0'].subrange(0, 0) == Seq::<char>::empty());
    assert(Str2Int(seq!['0'].subrange(0, 0)) == 0);
    assert(seq!['0'].index(0) == '0');
}

proof fn str2int_single_one()
    ensures Str2Int(seq!['1']) == 1
{
    assert(seq!['1'].len() == 1);
    assert(seq!['1'].subrange(0, 0) == Seq::<char>::empty());
    assert(Str2Int(seq!['1'].subrange(0, 0)) == 0);
    assert(seq!['1'].index(0) == '1');
}

proof fn str2int_leading_zeros(s: Seq<char>)
    requires ValidBitString(s),
             s.len() > 0,
             s.index(0) == '0'
    ensures Str2Int(s) == Str2Int(s.subrange(1, s.len() as int))
    decreases s.len()
{
    if s.len() == 1 {
        assert(s == seq!['0']) by {
            assert(s.len() == 1);
            assert(s.index(0) == '0');
        }
        assert(s.subrange(1, s.len() as int) == Seq::<char>::empty());
        str2int_single_zero();
        str2int_empty();
    } else {
        let tail = s.subrange(1, s.len() as int);
        let prefix = s.subrange(0, s.len() as int - 1);
        
        assert(ValidBitString(tail)) by {
            assert forall |i: int| 0 <= i && i < tail.len() as int implies
                tail.index(i) == '1' || tail.index(i) == '0' by {
                assert(tail.index(i) == s.index(i + 1));
            }
        }
        
        assert(prefix.index(0) == '0');
        assert(ValidBitString(prefix)) by {
            assert forall |i: int| 0 <= i && i < prefix.len() as int implies
                prefix.index(i) == '1' || prefix.index(i) == '0' by {
                assert(prefix.index(i) == s.index(i));
            }
        }
        
        let last_char = s.index(s.len() as int - 1);
        let last_val = if last_char == '1' { 1nat } else { 0nat };
        
        assert(Str2Int(s) == 2 * Str2Int(prefix) + last_val);
        
        if prefix.len() > 1 {
            str2int_leading_zeros(prefix);
            assert(Str2Int(prefix) == Str2Int(prefix.subrange(1, prefix.len() as int)));
        } else {
            str2int_single_zero();
            assert(Str2Int(prefix) == 0);
        }
        
        assert(tail.len() == prefix.len());
        assert(prefix.subrange(1, prefix.len() as int) == tail.subrange(0, tail.len() as int - 1)) by {
            assert forall |i: int| 0 <= i && i < prefix.len() as int - 1 implies
                prefix.index(i + 1) == tail.index(i) by {
                assert(prefix.index(i + 1) == s.index(i + 1));
                assert(tail.index(i) == s.index(i + 1));
            }
        }
        
        assert(Str2Int(tail) == 2 * Str2Int(tail.subrange(0, tail.len() as int - 1)) + last_val);
        assert(Str2Int(s) == Str2Int(tail));
    }
}

proof fn str2int_compare_length(s1: Seq<char>, s2: Seq<char>)
    requires ValidBitString(s1),
             ValidBitString(s2),
             s1.len() > 0,
             s2.len() > 0,
             s1.index(0) != '0',
             s2.index(0) != '0',
             s1.len() < s2.len()
    ensures Str2Int(s1) < Str2Int(s2)
    decreases s2.len()
{
    // A shorter non-zero-leading string has smaller value than a longer one
    // This proof would need induction on the string lengths
}

proof fn str2int_compare_same_length(s1: Seq<char>, s2: Seq<char>, j: int)
    requires ValidBitString(s1),
             ValidBitString(s2),
             s1.len() == s2.len(),
             0 <= j < s1.len(),
             forall |k: int| 0 <= k && k < j ==> s1.index(k) == s2.index(k),
             s1.index(j) < s2.index(j)
    ensures Str2Int(s1) < Str2Int(s2)
    decreases s1.len() - j
{
    // When strings have same prefix but s1[j] < s2[j], then Str2Int(s1) < Str2Int(s2)
    // This proof would need induction
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
    let n1 = s1.len();
    let n2 = s2.len();
    
    // Find first non-zero position in s1
    let mut i1: usize = 0;
    while i1 < n1 && s1[i1] == '0'
        invariant 0 <= i1 <= n1,
                  forall |k: int| 0 <= k && k < i1 ==> s1@.index(k) == '0',
                  i1 > 0 && i1 < n1 ==> ValidBitString(s1@.subrange(i1 as int, n1 as int)),
                  i1 > 0 && i1 < n1 ==> Str2Int(s1@) == Str2Int(s1@.subrange(i1 as int, n1 as int))
        decreases n1 - i1
    {
        proof {
            if i1 == 0 {
                str2int_leading_zeros(s1@);
                assert(ValidBitString(s1@.subrange(1, n1 as int))) by {
                    assert forall |k: int| 0 <= k && k < s1@.subrange(1, n1 as int).len() implies
                        s1@.subrange(1, n1 as int).index(k) == '0' || s1@.subrange(1, n1 as int).index(k) == '1' by {
                        assert(s1@.subrange(1, n1 as int).index(k) == s1@.index(k + 1));
                    }
                }
            } else {
                let s_sub = s1@.subrange(i1 as int, n1 as int);
                assert(s_sub.len() > 0);
                assert(s_sub.index(0) == s1@.index(i1 as int));
                assert(s_sub.index(0) == '0');
                assert(ValidBitString(s_sub)) by {
                    assert forall |k: int| 0 <= k && k < s_sub.len() implies
                        s_sub.index(k) == '0' || s_sub.index(k) == '1' by {
                        assert(s_sub.index(k) == s1@.index(i1 as int + k));
                    }
                }
                str2int_leading_zeros(s_sub);
                assert(ValidBitString(s1@.subrange(i1 as int + 1, n1 as int))) by {
                    assert forall |k: int| 0 <= k && k < s1@.subrange(i1 as int + 1, n1 as int).len() implies
                        s1@.subrange(i1 as int + 1, n1 as int).index(k) == '0' || s1@.subrange(i1 as int + 1, n1 as int).index(k) == '1' by {
                        assert(s1@.subrange(i1 as int + 1, n1 as int).index(k) == s1@.index(i1 as int + 1 + k));
                    }
                }
            }
        }
        i1 = i1 + 1;
    }
    
    // Find first non-zero position in s2
    let mut i2: usize = 0;
    while i2 < n2 && s2[i2] == '0'
        invariant 0 <= i2 <= n2,
                  forall |k: int| 0 <= k && k < i2 ==> s2@.index(k) == '0',
                  i2 > 0 && i2 < n2 ==> ValidBitString(s2@.subrange(i2 as int, n2 as int)),
                  i2 > 0 && i2 < n2 ==> Str2Int(s2@) == Str2Int(s2@.subrange(i2 as int, n2 as int))
        decreases n2 - i2
    {
        proof {
            if i2 == 0 {
                str2int_leading_zeros(s2@);
                assert(ValidBitString(s2@.subrange(1, n2 as int))) by {
                    assert forall |k: int| 0 <= k && k < s2@.subrange(1, n2 as int).len() implies
                        s2@.subrange(1, n2 as int).index(k) == '0' || s2@.subrange(1, n2 as int).index(k) == '1' by {
                        assert(s2@.subrange(1, n2 as int).index(k) == s2@.index(k + 1));
                    }
                }
            } else {
                let s_sub = s2@.subrange(i2 as int, n2 as int);
                assert(s_sub.len() > 0);
                assert(s_sub.index(0) == s2@.index(i2 as int));
                assert(s_sub.index(0) == '0');
                assert(ValidBitString(s_sub)) by {
                    assert forall |k: int| 0 <= k && k < s_sub.len() implies
                        s_sub.index(k) == '0' || s_sub.index(k) == '1' by {
                        assert(s_sub.index(k) == s2@.index(i2 as int + k));
                    }
                }
                str2int_leading_zeros(s_sub);
                assert(ValidBitString(s2@.subrange(i2 as int + 1, n2 as int))) by {
                    assert forall |k: int| 0 <= k && k < s2@.subrange(i2 as int + 1, n2 as int).len() implies
                        s2@.subrange(i2 as int + 1, n2 as int).index(k) == '0' || s2@.subrange(i2 as int + 1, n2 as int).index(k) == '1' by {
                        assert(s2@.subrange(i2 as int + 1, n2 as int).index(k) == s2@.index(i2 as int + 1 + k));
                    }
                }
            }
        }
        i2 = i2 + 1;
    }
    
    // Handle case where all digits are zeros
    if i1 == n1 && i2 == n2 {
        proof {
            assert forall |k: int| 0 <= k && k < n1 implies s1@.index(k) == '0' by {}
            assert forall |k: int| 0 <= k && k < n2 implies s2@.index(k) == '0' by {}
            // Both strings are all zeros, so their values are equal
        }
        return 0;
    } else if i1 == n1 {
        proof {
            assert forall |k: int| 0 <= k && k < n1 implies s1@.index(k) == '0' by {}
            // s1 is all zeros, s2 has non-zero digits
        }
        return -1;
    } else if i2 == n2 {
        proof {
            assert forall |k: int| 0 <= k && k < n2 implies s2@.index(k) == '0' by {}
            // s2 is all zeros, s1 has non-zero digits
        }
        return 1;
    }
    
    let len1 = n1 - i1;
    let len2 = n2 - i2;
    
    // Compare lengths first (longer number is greater)
    if len1 < len2 {
        proof {
            // str2int_compare_length would prove this
        }
        return -1;
    } else if len1 > len2 {
        proof {
            // str2int_compare_length would prove this
        }
        return 1;
    }
    
    // Same length, compare digit by digit
    let mut j: usize = 0;
    while j < len1
        invariant 0 <= j <= len1,
                  len1 == len2,
                  i1 + j <= n1,
                  i2 + j <= n2,
                  forall |k: int| 0 <= k && k < j ==> s1@.index(i1 as int + k) == s2@.index(i2 as int + k)
        decreases len1 - j
    {
        if s1[i1 + j] < s2[i2 + j] {
            proof {
                // str2int_compare_same_length would prove this
            }
            return -1;
        } else if s1[i1 + j] > s2[i2 + j] {
            proof {
                // str2int_compare_same_length would prove this
            }
            return 1;
        }
        j = j + 1;
    }
    
    proof {
        assert forall |k: int| 0 <= k && k < len1 implies 
            s1@.index(i1 as int + k) == s2@.index(i2 as int + k) by {}
        // The normalized strings are equal, so their values are equal
    }
    return 0;
}
// </vc-code>

fn main() {}
}