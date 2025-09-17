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
    } else {
        lemma_str2int_prefix_equal(s1, s2, k - 1);
        let s1_prefix = s1.subrange(0, k);
        let s2_prefix = s2.subrange(0, k);
        
        assert(s1_prefix.index((k-1) as int) == s1[(k-1) as int]);
        assert(s2_prefix.index((k-1) as int) == s2[(k-1) as int]);
        assert(s1[(k-1) as int] == s2[(k-1) as int]);
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
    let len = s1.len() as int;
    
    lemma_str2int_prefix_equal(s1, s2, k);
    lemma_str2int_suffix_bound(s1.subrange(k+1, len));
    lemma_str2int_suffix_bound(s2.subrange(k+1, len));
    
    let suffix_len = len - k - 1;
    
    lemma_str2int_decomposition(s1, k);
    lemma_str2int_decomposition(s2, k);
    
    if s1[k] == '0' && s2[k] == '1' {
        assert(Str2Int(s1.subrange(k+1, len)) < nat_pow(2, suffix_len as nat));
        assert(Str2Int(s1) < Str2Int(s2));
    } else if s1[k] == '1' && s2[k] == '0' {
        assert(Str2Int(s2.subrange(k+1, len)) < nat_pow(2, suffix_len as nat));
        assert(Str2Int(s1) > Str2Int(s2));
    }
}

proof fn lemma_str2int_decomposition(s: Seq<char>, k: int)
    requires ValidBitString(s), 0 <= k < s.len()
    ensures 
        Str2Int(s) == nat_pow(2, (s.len() - k - 1) as nat) * (2 * Str2Int(s.subrange(0, k)) + (if s[k] == '1' { 1nat } else { 0nat })) + Str2Int(s.subrange(k+1, s.len() as int))
    decreases s.len() - k
{
    let len = s.len() as int;
    if k + 1 == len {
        assert(s.subrange(k+1, len) =~= Seq::<char>::empty());
        assert(Str2Int(s.subrange(k+1, len)) == 0);
        assert(nat_pow(2, 0) == 1);
        lemma_str2int_split_at(s, k);
    } else {
        let s_without_last = s.subrange(0, len - 1);
        lemma_str2int_decomposition(s_without_last, k);
        lemma_str2int_split_at(s, len - 1);
        
        assert(s.index(len - 1) == s[(len - 1) as int]);
        assert(Str2Int(s) == 2 * Str2Int(s_without_last) + (if s.index(len - 1) == '1' { 1nat } else { 0nat }));
    }
}

proof fn lemma_str2int_split_at(s: Seq<char>, pos: int)
    requires ValidBitString(s), 0 <= pos < s.len()
    ensures 
        pos == s.len() - 1 ==> Str2Int(s) == 2 * Str2Int(s.subrange(0, pos)) + (if s[pos] == '1' { 1nat } else { 0nat })
    decreases s.len()
{
    if pos == s.len() - 1 {
        assert(s.subrange(0, pos) =~= s.subrange(0, s.len() as int - 1));
        assert(s[pos] == s.index(s.len() as int - 1));
    }
}

proof fn lemma_str2int_suffix_bound(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) < nat_pow(2, s.len() as nat)
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
        assert(Str2Int(prefix) < nat_pow(2, prefix.len() as nat));
        assert(2 * Str2Int(prefix) < 2 * nat_pow(2, prefix.len() as nat));
        assert(2 * nat_pow(2, prefix.len() as nat) == nat_pow(2, s.len() as nat));
        assert(Str2Int(s) <= 2 * Str2Int(prefix) + 1);
        assert(Str2Int(s) < nat_pow(2, s.len() as nat));
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
        s2.len() > 0,
        exists |i: int| 0 <= i < s2.len() && s2[i] == '1'
    ensures Str2Int(s1) < Str2Int(s2)
{
    lemma_str2int_suffix_bound(s1);
    lemma_str2int_has_one_lower_bound(s2);
    assert(Str2Int(s1) < nat_pow(2, s1.len() as nat));
    let first_one = choose |i: int| 0 <= i < s2.len() && s2[i] == '1';
    assert(Str2Int(s2) >= nat_pow(2, (s2.len() - 1 - first_one) as nat));
    
    if s1.len() == 0 {
        assert(Str2Int(s1) == 0);
        assert(Str2Int(s2) >= 1);
    } else {
        lemma_power_monotonic(2, s1.len() as nat, s2.len() as nat);
        assert(nat_pow(2, s1.len() as nat) <= nat_pow(2, s2.len() as nat));
        assert(nat_pow(2, (s2.len() - 1 - first_one) as nat) >= 1);
        assert(Str2Int(s2) >= 1);
        if s1.len() < s2.len() - first_one {
            assert(nat_pow(2, s1.len() as nat) <= nat_pow(2, (s2.len() - 1 - first_one) as nat));
        }
    }
}

proof fn lemma_str2int_has_one_lower_bound(s: Seq<char>)
    requires ValidBitString(s), exists |i: int| 0 <= i < s.len() && s[i] == '1'
    ensures Str2Int(s) >= 1
    decreases s.len()
{
    if s.len() == 0 {
        assert(false);
    } else if s.len() == 1 {
        let first_one = choose |i: int| 0 <= i < s.len() && s[i] == '1';
        assert(first_one == 0);
        assert(s[0] == '1');
        assert(Str2Int(s) == 1);
    } else {
        let last_bit = s.index(s.len() as int - 1);
        let prefix = s.subrange(0, s.len() as int - 1);
        
        if last_bit == '1' {
            assert(Str2Int(s) >= 1);
        } else {
            assert(exists |i: int| 0 <= i < prefix.len() && prefix[i] == '1');
            lemma_str2int_has_one_lower_bound(prefix);
            assert(Str2Int(prefix) >= 1);
            assert(Str2Int(s) == 2 * Str2Int(prefix));
            assert(Str2Int(s) >= 2);
        }
    }
}

proof fn lemma_power_monotonic(base: nat, exp1: nat, exp2: nat)
    requires base >= 1, exp1 <= exp2
    ensures nat_pow(base, exp1) <= nat_pow(base, exp2)
    decreases exp2
{
    if exp1 == exp2 {
        return;
    } else if exp1 == 0 {
        assert(nat_pow(base, 0) == 1);
        lemma_power_positive(base, exp2);
    } else {
        lemma_power_monotonic(base, (exp1 - 1) as nat, (exp2 - 1) as nat);
        lemma_mult_monotonic(base, nat_pow(base, (exp1 - 1) as nat), nat_pow(base, (exp2 - 1) as nat));
    }
}

proof fn lemma_power_positive(base: nat, exp: nat)
    requires base >= 1
    ensures nat_pow(base, exp) >= 1
    decreases exp
{
    if exp == 0 {
        assert(nat_pow(base, 0) == 1);
    } else {
        lemma_power_positive(base, (exp - 1) as nat);
    }
}

proof fn lemma_mult_monotonic(a: nat, b: nat, c: nat)
    requires b <= c
    ensures a * b <= a * c
{
}

proof fn lemma_equal_strings_equal_values(s1: Seq<char>, s2: Seq<char>)
    requires ValidBitString(s1), ValidBitString(s2), s1 == s2
    ensures Str2Int(s1) == Str2Int(s2)
{
}

proof fn lemma_all_zeros_value_zero(s: Seq<char>)
    requires ValidBitString(s), forall |i: int| 0 <= i < s.len() ==> s[i] == '0'
    ensures Str2Int(s) == 0
    decreases s.len()
{
    if s.len() == 0 {
        assert(Str2Int(s) == 0);
    } else {
        let prefix = s.subrange(0, s.len() as int - 1);
        lemma_all_zeros_value_zero(prefix);
        assert(s.index(s.len() as int - 1) == '0');
        assert(Str2Int(s) == 2 * Str2Int(prefix) + 0);
        assert(Str2Int(s) == 0);
    }
}

proof fn lemma_nonzero_has_one(s: Seq<char>)
    requires ValidBitString(s), Str2Int(s) > 0
    ensures exists |i: int| 0 <= i < s.len() && s[i] == '1'
{
    if !(exists |i: int| 0 <= i < s.len() && s[i] == '1') {
        assert(forall |i: int| 0 <= i < s.len() ==> s[i] == '0');
        lemma_all_zeros_value_zero(s);
        assert(Str2Int(s) == 0);
        assert(false);
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
    
    // First compare by length
    if len1 < len2 {
        proof {
            if Str2Int(s2@) > 0 {
                lemma_nonzero_has_one(s2@);
                lemma_shorter_string_smaller(s1@, s2@);
            } else {
                lemma_str2int_suffix_bound(s1@);
                assert(Str2Int(s1@) >= 0);
                assert(Str2Int(s1@) < Str2Int(s2@));
            }
        }
        return -1;
    } else if len1 > len2 {
        proof {
            if Str2Int(s1@) > 0 {
                lemma_nonzero_has_one(s1@);
                lemma_shorter_string_smaller(s2@, s1@);
            } else {
                lemma_str2int_suffix_bound(s2@);
                assert(Str2Int(s2@) >= 0);
                assert(Str2Int(s1@) > Str2Int(s2@));
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
            forall |j: int| 0 <= j < i ==> #[trigger] s1@[j] == s2@[j],
            s1@.len() == len1,
            s2@.len() == len2
        decreases len1 - i
    {
        if s1[i] == '0' && s2[i] == '1' {
            proof {
                assert(0 <= i < s1@.len());
                assert(s1@[i as int] == '0' && s2@[i as int] == '1');
                assert(s1@ != s2@);
                assert(exists |k: int| 0 <= k < s1@.len() && s1@[k] != s2@[k] && 
                    (forall |j: int| 0 <= j < k ==> s1@[j] == s2@[j]));
                lemma_str2int_monotonic(s1@, s2@);
            }
            return -1;
        } else if s1[i] == '1' && s2[i] == '0' {
            proof {
                assert(0 <= i < s1@.len());
                assert(s1@[i as int] == '1' && s2@[i as int] == '0');
                assert(s1@ != s2@);
                assert(exists |k: int| 0 <= k < s1@.len() && s1@[k] != s2@[k] && 
                    (forall |j: int| 0 <= j < k ==> s1@[j] == s2@[j]));
                lemma_str2int_monotonic(s1@, s2@);
            }
            return 1;
        }
        i += 1;
    }
    
    proof {
        assert(len1 == s1@.len());
        assert(forall |j: int| 0 <= j < s1@.len() ==> s1@[j] == s2@[j]);
        assert(s1@ == s2@);
        lemma_equal_strings_equal_values(s1@, s2@);
    }
    return 0;
}
// </vc-code>

fn main() {}
}