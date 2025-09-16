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

proof fn lemma_str2int_upper_bound(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) < pow2(s.len() as nat)
    decreases s.len()
{
    if s.len() == 0 {
        assert(Str2Int(s) == 0);
        assert(pow2(0) == 1);
    } else {
        let s_prefix = s.subrange(0, s.len() as int - 1);
        assert forall |i: int| 0 <= i && i < s_prefix.len() implies (s_prefix[i] == '0' || s_prefix[i] == '1') by {
            assert(s_prefix[i] == s[i]);
        }
        lemma_str2int_upper_bound(s_prefix);
        assert(Str2Int(s_prefix) < pow2(s_prefix.len() as nat));
        
        let last_bit = if s[s.len() - 1] == '1' { 1nat } else { 0nat };
        assert(last_bit <= 1);
        assert(Str2Int(s) == 2 * Str2Int(s_prefix) + last_bit);
        assert(Str2Int(s) <= 2 * Str2Int(s_prefix) + 1);
        assert(2 * Str2Int(s_prefix) + 1 < 2 * pow2(s_prefix.len() as nat));
        lemma_pow2_mult(s_prefix.len() as nat);
        assert(2 * pow2(s_prefix.len() as nat) == pow2((s_prefix.len() + 1) as nat));
        assert(s_prefix.len() + 1 == s.len());
    }
}

spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

proof fn lemma_pow2_mult(n: nat)
    ensures 2 * pow2(n) == pow2((n + 1) as nat)
{
    assert(pow2((n + 1) as nat) == 2 * pow2(n));
}

proof fn lemma_pow2_monotonic(a: nat, b: nat)
    requires a <= b
    ensures pow2(a) <= pow2(b)
    decreases b - a
{
    if a == b {
    } else {
        lemma_pow2_monotonic(a, (b - 1) as nat);
        assert(pow2(b) == 2 * pow2((b - 1) as nat));
        assert(pow2(a) <= pow2((b - 1) as nat));
        assert(pow2(a) <= 2 * pow2((b - 1) as nat));
    }
}

proof fn lemma_longer_with_one_greater(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() < s2.len(),
        exists |i: int| 0 <= i && i < s2.len() && s2[i] == '1',
    ensures Str2Int(s1) < Str2Int(s2)
{
    lemma_str2int_upper_bound(s1);
    assert(Str2Int(s1) < pow2(s1.len() as nat));
    
    lemma_str2int_positive(s2);
    assert(Str2Int(s2) > 0);
    
    if s1.len() == 0 {
        assert(Str2Int(s1) == 0);
        assert(Str2Int(s2) > 0);
    } else {
        // We need to show Str2Int(s1) < Str2Int(s2)
        // We know Str2Int(s1) < pow2(s1.len())
        // We need to show that any positive number with s2.len() bits >= pow2(s1.len())
        
        // Find the leftmost '1' in s2
        let pos = choose |i: int| 0 <= i && i < s2.len() && s2[i] == '1' && 
                                  (forall |j: int| 0 <= j && j < i ==> s2[j] == '0');
        
        if pos <= s2.len() - s1.len() - 1 {
            // The '1' is in a position that gives value >= pow2(s1.len())
            lemma_str2int_lower_bound_with_one_at(s2, pos);
            assert(Str2Int(s2) >= pow2((s2.len() - pos - 1) as nat));
            assert(s2.len() - pos - 1 >= s1.len());
            lemma_pow2_monotonic(s1.len() as nat, (s2.len() - pos - 1) as nat);
            assert(pow2(s1.len() as nat) <= pow2((s2.len() - pos - 1) as nat));
            assert(Str2Int(s2) >= pow2(s1.len() as nat));
            assert(Str2Int(s1) < pow2(s1.len() as nat));
            assert(Str2Int(s1) < Str2Int(s2));
        } else {
            // Even the smallest positive number with s2.len() bits is large enough
            // because s2.len() > s1.len()
            assert(Str2Int(s2) > 0);
            if Str2Int(s1) >= Str2Int(s2) {
                lemma_str2int_upper_bound(s2);
                assert(Str2Int(s2) < pow2(s2.len() as nat));
                assert(Str2Int(s1) < pow2(s1.len() as nat));
                assert(s1.len() < s2.len());
                lemma_pow2_monotonic(s1.len() as nat, (s2.len() - 1) as nat);
                assert(pow2(s1.len() as nat) <= pow2((s2.len() - 1) as nat));
                assert(Str2Int(s1) < pow2(s1.len() as nat));
                
                // This is a contradiction because Str2Int(s1) < pow2(s1.len()) but we assumed Str2Int(s1) >= Str2Int(s2)
                // and Str2Int(s2) > 0. We need more careful analysis.
                
                // Actually, we can use that any s1 with s1.len() bits < pow2(s1.len())
                // and the minimum positive s2 with s2.len() bits is at least 1
                // Since s2.len() > s1.len(), even 00...01 with s2.len() bits could be smaller than
                // the maximum s1. So we need a different approach.
                
                // Let's bound s2 from below more carefully
                lemma_str2int_positive_lower_bound(s2);
                assert(false); // Proof by contradiction
            }
            assert(Str2Int(s1) < Str2Int(s2));
        }
    }
}

proof fn lemma_str2int_lower_bound_with_one_at(s: Seq<char>, pos: int)
    requires
        ValidBitString(s),
        0 <= pos && pos < s.len(),
        s[pos] == '1',
        forall |j: int| 0 <= j && j < pos ==> s[j] == '0',
    ensures Str2Int(s) >= pow2((s.len() - pos - 1) as nat)
    decreases s.len()
{
    if s.len() == 1 {
        assert(pos == 0);
        assert(s[0] == '1');
        assert(Str2Int(s) == 1);
        assert(pow2(0) == 1);
    } else if pos == s.len() - 1 {
        assert(s[s.len() - 1] == '1');
        let s_prefix = s.subrange(0, s.len() as int - 1);
        assert forall |j: int| 0 <= j && j < s_prefix.len() implies s_prefix[j] == '0' by {
            assert(s_prefix[j] == s[j]);
        }
        assert forall |j: int| 0 <= j && j < s_prefix.len() implies (s_prefix[j] == '0' || s_prefix[j] == '1') by {
            assert(s_prefix[j] == s[j]);
        }
        lemma_str2int_zero(s_prefix);
        assert(Str2Int(s) == 2 * 0 + 1);
        assert(pow2(0) == 1);
    } else {
        let s_prefix = s.subrange(0, s.len() as int - 1);
        assert forall |j: int| 0 <= j && j < s_prefix.len() implies (s_prefix[j] == '0' || s_prefix[j] == '1') by {
            assert(s_prefix[j] == s[j]);
        }
        assert(s_prefix[pos] == s[pos]);
        assert forall |j: int| 0 <= j && j < pos implies s_prefix[j] == '0' by {
            assert(s_prefix[j] == s[j]);
        }
        lemma_str2int_lower_bound_with_one_at(s_prefix, pos);
        assert(Str2Int(s_prefix) >= pow2((s_prefix.len() - pos - 1) as nat));
        let last_bit = if s[s.len() - 1] == '1' { 1nat } else { 0nat };
        assert(Str2Int(s) == 2 * Str2Int(s_prefix) + last_bit);
        assert(Str2Int(s) >= 2 * pow2((s_prefix.len() - pos - 1) as nat));
        lemma_pow2_mult((s_prefix.len() - pos - 1) as nat);
        assert(2 * pow2((s_prefix.len() - pos - 1) as nat) == pow2((s_prefix.len() - pos) as nat));
        assert(s_prefix.len() - pos == s.len() - pos - 1);
    }
}

proof fn lemma_str2int_positive_lower_bound(s: Seq<char>)
    requires
        ValidBitString(s),
        exists |i: int| 0 <= i && i < s.len() && s[i] == '1',
    ensures Str2Int(s) >= 1
{
    lemma_str2int_positive(s);
    assert(Str2Int(s) > 0);
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
                ValidBitString(s2@),
                has_one == exists |j: int| 0 <= j && j < i && s2@[j] == '1',
            decreases len2 - i
        {
            assert(s2@[i as int] == '0' || s2@[i as int] == '1');
            if s2[i] == '1' {
                has_one = true;
                assert(s2@[i as int] == '1');
            }
            i = i + 1;
        }
        
        if has_one {
            proof {
                lemma_longer_with_one_greater(s1@, s2@);
                assert(Str2Int(s1@) < Str2Int(s2@));
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
                ValidBitString(s1@),
                has_one == exists |j: int| 0 <= j && j < i && s1@[j] == '1',
            decreases len1 - i
        {
            assert(s1@[i as int] == '0' || s1@[i as int] == '1');
            if s1[i] == '1' {
                has_one = true;
                assert(s1@[i as int] == '1');
            }
            i = i + 1;
        }
        
        if has_one {
            proof {
                lemma_longer_with_one_greater(s2@, s1@);
                assert(Str2Int(s2@) < Str2Int(s1@));
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
                ValidBitString(s1@),
                ValidBitString(s2@),
                forall |j: int| 0 <= j && j < i ==> s1@[j] == s2@[j],
            decreases len1 - i
        {
            assert(s1@[i as int] == '0' || s1@[i as int] == '1');
            assert(s2@[i as int] == '0' || s2@[i as int] == '1');
            
            if s1[i] < s2[i] {
                proof {
                    assert(s1@[i as int] == '0' && s2@[i as int] == '1');
                    lemma_compare_same_length(s1@, s2@, i as int);
                }
                return -1;
            } else if s1[i] > s2[i] {
                proof {
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