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
proof fn lemma_str2int_monotonic(s1: Seq<char>, s2: Seq<char>)
    requires 
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() == s2.len(),
        s1 != s2,
        exists |i: int| 0 <= i < s1.len() && s1[i] != s2[i] && 
            (forall |j: int| 0 <= j < i ==> s1[j] == s2[j])
    ensures 
        (exists |i: int| 0 <= i < s1.len() && s1[i] == '0' && s2[i] == '1' && 
            (forall |j: int| 0 <= j < i ==> s1[j] == s2[j])) ==> Str2Int(s1) < Str2Int(s2),
        (exists |i: int| 0 <= i < s1.len() && s1[i] == '1' && s2[i] == '0' && 
            (forall |j: int| 0 <= j < i ==> s1[j] == s2[j])) ==> Str2Int(s1) > Str2Int(s2)
{
    let diff_pos = choose |i: int| 0 <= i < s1.len() && s1[i] != s2[i] && 
        (forall |j: int| 0 <= j < i ==> s1[j] == s2[j]);
    
    lemma_str2int_prefix_equal(s1, s2, diff_pos);
    lemma_str2int_bit_difference(s1, s2, diff_pos);
}

proof fn lemma_str2int_prefix_equal(s1: Seq<char>, s2: Seq<char>, k: int)
    requires 
        ValidBitString(s1),
        ValidBitString(s2),
        0 <= k <= s1.len(),
        k <= s2.len(),
        forall |j: int| 0 <= j < k ==> s1[j] == s2[j]
    ensures 
        Str2Int(s1.subrange(0, k)) == Str2Int(s2.subrange(0, k))
    decreases k
{
    if k == 0 {
        assert(s1.subrange(0, 0) == Seq::<char>::empty());
        assert(s2.subrange(0, 0) == Seq::<char>::empty());
        assert(Str2Int(s1.subrange(0, 0)) == 0);
        assert(Str2Int(s2.subrange(0, 0)) == 0);
    } else {
        lemma_str2int_prefix_equal(s1, s2, k - 1);
        let s1_prefix = s1.subrange(0, k);
        let s2_prefix = s2.subrange(0, k);
        let s1_prefix_minus1 = s1.subrange(0, k-1);
        let s2_prefix_minus1 = s2.subrange(0, k-1);
        
        assert(s1_prefix.index(k-1) == s1[k-1]);
        assert(s2_prefix.index(k-1) == s2[k-1]);
        assert(s1[k-1] == s2[k-1]);
        assert(s1_prefix.subrange(0, k-1) == s1_prefix_minus1);
        assert(s2_prefix.subrange(0, k-1) == s2_prefix_minus1);
        
        assert(Str2Int(s1_prefix) == 2 * Str2Int(s1_prefix_minus1) + (if s1_prefix.index(k-1) == '1' { 1nat } else { 0nat }));
        assert(Str2Int(s2_prefix) == 2 * Str2Int(s2_prefix_minus1) + (if s2_prefix.index(k-1) == '1' { 1nat } else { 0nat }));
    }
}

proof fn lemma_str2int_bit_difference(s1: Seq<char>, s2: Seq<char>, k: int)
    requires 
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() == s2.len(),
        0 <= k < s1.len(),
        forall |j: int| 0 <= j < k ==> s1[j] == s2[j],
        s1[k] != s2[k]
    ensures 
        s1[k] == '0' && s2[k] == '1' ==> Str2Int(s1) < Str2Int(s2),
        s1[k] == '1' && s2[k] == '0' ==> Str2Int(s1) > Str2Int(s2)
{
    let len = s1.len();
    
    lemma_str2int_prefix_equal(s1, s2, k);
    lemma_str2int_suffix_bound(s1.subrange(k+1, len as int));
    lemma_str2int_suffix_bound(s2.subrange(k+1, len as int));
    
    let prefix_len = k;
    let suffix_len = len - k - 1;
    let prefix1 = s1.subrange(0, k);
    let prefix2 = s2.subrange(0, k);
    let suffix1 = s1.subrange(k+1, len as int);
    let suffix2 = s2.subrange(k+1, len as int);
    
    // Express Str2Int in terms of prefix, bit k, and suffix
    assert(Str2Int(s1) == nat_pow(2, suffix_len) * (2 * Str2Int(prefix1) + (if s1[k] == '1' { 1nat } else { 0nat })) + Str2Int(suffix1));
    assert(Str2Int(s2) == nat_pow(2, suffix_len) * (2 * Str2Int(prefix2) + (if s2[k] == '1' { 1nat } else { 0nat })) + Str2Int(suffix2));
    
    // Since prefixes are equal
    assert(Str2Int(prefix1) == Str2Int(prefix2));
    
    if s1[k] == '0' && s2[k] == '1' {
        let diff = nat_pow(2, suffix_len);
        assert(Str2Int(s2) >= Str2Int(s1) + diff);
        assert(Str2Int(suffix1) < nat_pow(2, suffix_len));
        assert(Str2Int(s1) < Str2Int(s2));
    } else if s1[k] == '1' && s2[k] == '0' {
        let diff = nat_pow(2, suffix_len);
        assert(Str2Int(s1) >= Str2Int(s2) + diff);
        assert(Str2Int(suffix2) < nat_pow(2, suffix_len));
        assert(Str2Int(s1) > Str2Int(s2));
    }
}

proof fn lemma_str2int_suffix_bound(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) < nat_pow(2, s.len())
    decreases s.len()
{
    if s.len() == 0 {
        assert(Str2Int(s) == 0);
        assert(nat_pow(2, 0) == 1);
    } else {
        let prefix = s.subrange(0, s.len() as int - 1);
        let last_bit = s.index(s.len() as int - 1);
        lemma_str2int_suffix_bound(prefix);
        
        assert(Str2Int(s) == 2 * Str2Int(prefix) + (if last_bit == '1' { 1nat } else { 0nat }));
        assert(Str2Int(prefix) < nat_pow(2, prefix.len()));
        assert(2 * Str2Int(prefix) < 2 * nat_pow(2, prefix.len()));
        assert(2 * nat_pow(2, prefix.len()) == nat_pow(2, s.len()));
        assert(Str2Int(s) <= 2 * Str2Int(prefix) + 1);
        assert(Str2Int(s) < nat_pow(2, s.len()));
    }
}

spec fn nat_pow(base: nat, exp: nat) -> nat
    decreases exp
{
    if exp == 0 { 1 } else { base * nat_pow(base, (exp - 1) as nat) }
}

proof fn lemma_shorter_string_smaller(s1: Seq<char>, s2: Seq<char>)
    requires 
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() < s2.len(),
        s2.len() > 0
    ensures Str2Int(s1) < Str2Int(s2)
{
    lemma_str2int_suffix_bound(s1);
    lemma_str2int_lower_bound(s2);
    assert(Str2Int(s1) < nat_pow(2, s1.len()));
    assert(Str2Int(s2) >= nat_pow(2, (s2.len() - 1) as nat));
    if s1.len() > 0 {
        lemma_power_monotonic(2, s1.len(), (s2.len() - 1) as nat);
    }
    assert(nat_pow(2, s1.len()) <= nat_pow(2, (s2.len() - 1) as nat));
}

proof fn lemma_str2int_lower_bound(s: Seq<char>)
    requires ValidBitString(s), s.len() > 0
    ensures Str2Int(s) >= nat_pow(2, (s.len() - 1) as nat)
    decreases s.len()
{
    if s.len() == 1 {
        assert(s[0] == '0' || s[0] == '1');
        if s[0] == '0' {
            assert(Str2Int(s) == 0);
            assert(nat_pow(2, 0) == 1);
            assert(false);  // This case is impossible for the lower bound
        } else {
            assert(Str2Int(s) == 1);
            assert(nat_pow(2, 0) == 1);
        }
    } else {
        let prefix = s.subrange(0, s.len() as int - 1);
        let last_bit = s.index(s.len() as int - 1);
        
        assert(Str2Int(s) == 2 * Str2Int(prefix) + (if last_bit == '1' { 1nat } else { 0nat }));
        assert(Str2Int(prefix) >= 0);
        assert(Str2Int(s) >= 2 * Str2Int(prefix));
        
        if prefix.len() > 0 && exists |i: int| 0 <= i < prefix.len() && prefix[i] == '1' {
            lemma_str2int_lower_bound(prefix);
            assert(Str2Int(prefix) >= nat_pow(2, (prefix.len() - 1) as nat));
            assert(2 * Str2Int(prefix) >= 2 * nat_pow(2, (prefix.len() - 1) as nat));
            assert(2 * nat_pow(2, (prefix.len() - 1) as nat) == nat_pow(2, prefix.len()));
            assert(nat_pow(2, prefix.len()) == nat_pow(2, (s.len() - 1) as nat));
        } else {
            // If first bit is '1', then we have the minimum value
            if s[0] == '1' {
                assert(Str2Int(s) >= nat_pow(2, (s.len() - 1) as nat));
            }
        }
    }
}

proof fn lemma_power_monotonic(base: nat, exp1: nat, exp2: nat)
    requires base > 1, exp1 <= exp2
    ensures nat_pow(base, exp1) <= nat_pow(base, exp2)
    decreases exp2 - exp1
{
    if exp1 == exp2 {
        return;
    } else if exp1 == 0 {
        assert(nat_pow(base, 0) == 1);
        assert(nat_pow(base, exp2) >= 1);
    } else {
        lemma_power_monotonic(base, exp1 - 1, exp2 - 1);
        assert(nat_pow(base, exp1 - 1) <= nat_pow(base, exp2 - 1));
        assert(nat_pow(base, exp1) == base * nat_pow(base, exp1 - 1));
        assert(nat_pow(base, exp2) == base * nat_pow(base, exp2 - 1));
        assert(base * nat_pow(base, exp1 - 1) <= base * nat_pow(base, exp2 - 1));
    }
}

proof fn lemma_equal_strings_equal_values(s1: Seq<char>, s2: Seq<char>)
    requires ValidBitString(s1), ValidBitString(s2), s1 == s2
    ensures Str2Int(s1) == Str2Int(s2)
{
    assert(s1 == s2);
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
    
    // First compare by length
    if len1 < len2 {
        proof {
            if len2 > 0 {
                lemma_shorter_string_smaller(s1@, s2@);
            }
        }
        return -1;
    } else if len1 > len2 {
        proof {
            if len1 > 0 {
                lemma_shorter_string_smaller(s2@, s1@);
            }
        }
        return 1;
    }
    
    // Same length, compare bit by bit from left to right
    let mut i = 0;
    while i < len1
        invariant 
            0 <= i <= len1,
            len1 == len2,
            ValidBitString(s1@),
            ValidBitString(s2@),
            forall |j: int| 0 <= j < i ==> #[trigger] s1@[j] == s2@[j]
        decreases len1 - i
    {
        assert(i < len1);
        assert(i < len2);
        if s1[i] == '0' && s2[i] == '1' {
            proof {
                assert(s1@[i as int] == '0' && s2@[i as int] == '1');
                assert(exists |k: int| 0 <= k < s1@.len() && s1@[k] != s2@[k] && 
                    (forall |j: int| 0 <= j < k ==> s1@[j] == s2@[j]));
                lemma_str2int_monotonic(s1@, s2@);
            }
            return -1;
        } else if s1[i] == '1' && s2[i] == '0' {
            proof {
                assert(s1@[i as int] == '1' && s2@[i as int] == '0');
                assert(exists |k: int| 0 <= k < s1@.len() && s1@[k] != s2@[k] && 
                    (forall |j: int| 0 <= j < k ==> s1@[j] == s2@[j]));
                lemma_str2int_monotonic(s1@, s2@);
            }
            return 1;
        }
        i += 1;
    }
    
    proof {
        assert(forall |j: int| 0 <= j < s1@.len() ==> s1@[j] == s2@[j]);
        assert(s1@ == s2@);
        lemma_equal_strings_equal_values(s1@, s2@);
    }
    return 0;
}
// </vc-code>

fn main() {}
}