use vstd::prelude::*;

verus! {

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 { 0 } else { 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }) }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==> (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
proof fn lemma_pow2_positive(n: nat)
    ensures pow2(n) >= 1,
    decreases n,
{
    if n == 0 {
        assert(pow2(0) == 1);
    } else {
        lemma_pow2_positive((n - 1) as nat);
        assert(pow2(n) == 2 * pow2((n - 1) as nat));
        assert(pow2((n - 1) as nat) >= 1);
        assert(pow2(n) >= 2);
    }
}

proof fn lemma_pow2_basic()
    ensures 
        pow2(0) == 1,
        pow2(1) == 2,
        pow2(2) == 4,
{
    assert(pow2(0) == 1);
    assert(pow2(1) == 2 * pow2(0) == 2 * 1 == 2);
    assert(pow2(2) == 2 * pow2(1) == 2 * 2 == 4);
}

proof fn lemma_str2int_single_char(s: Seq<char>)
    requires
        ValidBitString(s),
        s.len() == 1,
    ensures
        s[0] == '0' ==> Str2Int(s) == 0,
        s[0] == '1' ==> Str2Int(s) == 1,
{
    if s.len() == 1 {
        assert(s.subrange(0, 0).len() == 0);
        assert(Str2Int(s.subrange(0, 0)) == 0);
        if s[0] == '0' {
            assert(Str2Int(s) == 2 * 0 + 0 == 0);
        } else {
            assert(s[0] == '1');
            assert(Str2Int(s) == 2 * 0 + 1 == 1);
        }
    }
}

proof fn lemma_longer_string_larger_value(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() > 0,
        s2.len() > 0,
        s1.len() > s2.len(),
        s1.len() > 1 ==> s1[0] != '0',
        s2.len() > 1 ==> s2[0] != '0',
    ensures
        Str2Int(s1) > Str2Int(s2),
    decreases s1.len(),
{
    if s2.len() == 1 {
        // s2 is single digit, so Str2Int(s2) is either 0 or 1
        lemma_str2int_single_char(s2);
        
        // s1 has length > 1, and s1[0] != '0'
        assert(s1.len() >= 2);
        assert(s1[0] == '1');
        
        // For any binary string starting with '1' and length >= 2,
        // its value is at least 2 (binary "10" = 2)
        lemma_min_value_for_length(s1);
        lemma_pow2_basic();
        assert(pow2((s1.len() - 1) as nat) >= pow2(1) == 2);
        assert(Str2Int(s1) >= 2);
        
        if s2[0] == '0' {
            assert(Str2Int(s2) == 0);
        } else {
            assert(Str2Int(s2) == 1);
        }
        assert(Str2Int(s1) > Str2Int(s2));
    } else {
        // Both strings have length > 1, so both start with '1'
        assert(s1[0] == '1');
        assert(s2[0] == '1');
        
        // A binary string of length n starting with '1' has minimum value 2^(n-1)
        // and maximum value 2^n - 1
        lemma_min_value_for_length(s1);
        lemma_max_value_for_length(s2);
        
        // Since s1.len() > s2.len(), we have:
        // Str2Int(s1) >= 2^(s1.len()-1) >= 2^s2.len() > 2^s2.len() - 1 >= Str2Int(s2)
        assert(Str2Int(s1) >= pow2((s1.len() - 1) as nat));
        assert(Str2Int(s2) <= pow2(s2.len() as nat) - 1);
        lemma_pow2_monotonic((s2.len() as nat), ((s1.len() - 1) as nat));
        assert(pow2((s1.len() - 1) as nat) >= pow2(s2.len() as nat));
        lemma_pow2_positive(s2.len() as nat);
        assert(pow2(s2.len() as nat) >= 1);
        assert(Str2Int(s1) > Str2Int(s2));
    }
}

spec fn pow2(n: nat) -> nat
    decreases n,
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

proof fn lemma_pow2_monotonic(a: nat, b: nat)
    requires a <= b,
    ensures pow2(a) <= pow2(b),
    decreases b,
{
    if a == b {
        assert(pow2(a) == pow2(b));
    } else if a == 0 {
        assert(pow2(a) == 1);
        lemma_pow2_positive(b);
        assert(pow2(b) >= 1);
    } else {
        lemma_pow2_monotonic((a - 1) as nat, (b - 1) as nat);
        assert(pow2(a) == 2 * pow2((a - 1) as nat));
        assert(pow2(b) == 2 * pow2((b - 1) as nat));
        assert(pow2(a) <= pow2(b));
    }
}

proof fn lemma_min_value_for_length(s: Seq<char>)
    requires
        ValidBitString(s),
        s.len() > 1,
        s[0] == '1',
    ensures
        Str2Int(s) >= pow2((s.len() - 1) as nat),
    decreases s.len(),
{
    lemma_pow2_basic();
    
    if s.len() == 2 {
        assert(s.subrange(0, 1).len() == 1);
        let s_prefix = s.subrange(0, 1);
        assert(s_prefix[0] == s[0] == '1');
        lemma_str2int_single_char(s_prefix);
        assert(Str2Int(s_prefix) == 1);
        
        if s[1] == '0' {
            assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, 1)) + 0);
            assert(Str2Int(s) == 2 * 1 == 2);
        } else {
            assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, 1)) + 1);
            assert(Str2Int(s) == 2 * 1 + 1 == 3);
        }
        assert(pow2(1) == 2);
        assert(Str2Int(s) >= 2);
        assert(Str2Int(s) >= pow2((s.len() - 1) as nat));
    } else {
        let s_prefix = s.subrange(0, s.len() as int - 1);
        assert(s_prefix.len() > 1);
        assert(s_prefix[0] == s[0] == '1');
        lemma_min_value_for_length(s_prefix);
        assert(Str2Int(s_prefix) >= pow2((s_prefix.len() - 1) as nat));
        
        if s[s.len() as int - 1] == '0' {
            assert(Str2Int(s) == 2 * Str2Int(s_prefix));
            assert(Str2Int(s) >= 2 * pow2((s_prefix.len() - 1) as nat));
        } else {
            assert(Str2Int(s) == 2 * Str2Int(s_prefix) + 1);
            assert(Str2Int(s) >= 2 * pow2((s_prefix.len() - 1) as nat));
        }
        assert(2 * pow2((s_prefix.len() - 1) as nat) == pow2(s_prefix.len() as nat));
        assert(s_prefix.len() == s.len() - 1);
        assert(Str2Int(s) >= pow2((s.len() - 1) as nat));
    }
}

proof fn lemma_max_value_for_length(s: Seq<char>)
    requires
        ValidBitString(s),
        s.len() > 0,
    ensures
        Str2Int(s) <= pow2(s.len() as nat) - 1,
    decreases s.len(),
{
    lemma_pow2_basic();
    
    if s.len() == 1 {
        lemma_str2int_single_char(s);
        if s[0] == '0' {
            assert(Str2Int(s) == 0);
        } else {
            assert(Str2Int(s) == 1);
        }
        assert(pow2(1) == 2);
        assert(Str2Int(s) <= 1);
        assert(Str2Int(s) <= pow2(s.len() as nat) - 1);
    } else {
        let s_prefix = s.subrange(0, s.len() as int - 1);
        lemma_max_value_for_length(s_prefix);
        assert(Str2Int(s_prefix) <= pow2(s_prefix.len() as nat) - 1);
        
        if s[s.len() as int - 1] == '0' {
            assert(Str2Int(s) == 2 * Str2Int(s_prefix));
            assert(Str2Int(s) <= 2 * (pow2(s_prefix.len() as nat) - 1));
            assert(Str2Int(s) <= 2 * pow2(s_prefix.len() as nat) - 2);
        } else {
            assert(Str2Int(s) == 2 * Str2Int(s_prefix) + 1);
            assert(Str2Int(s) <= 2 * (pow2(s_prefix.len() as nat) - 1) + 1);
            assert(Str2Int(s) <= 2 * pow2(s_prefix.len() as nat) - 1);
        }
        assert(2 * pow2(s_prefix.len() as nat) == pow2((s_prefix.len() + 1) as nat));
        assert(s_prefix.len() + 1 == s.len());
        assert(Str2Int(s) <= pow2(s.len() as nat) - 1);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn CompareUnequal(s1: &[char], s2: &[char]) -> (res: i32)
  requires ValidBitString(s1@), ValidBitString(s2@),
    s1@.len() > 0,
    (s1@.len() > 1 ==> s1@[0] != '0'),
    s2@.len() > 0,
    (s2@.len() > 1 ==> s2@[0] != '0'),
    s1@.len() > s2@.len()
  ensures (Str2Int(s1@) < Str2Int(s2@) ==> res == -1),
    (Str2Int(s1@) == Str2Int(s2@) ==> res == 0),
    (Str2Int(s1@) > Str2Int(s2@) ==> res == 1)
// </vc-spec>
// <vc-code>
{
    proof {
        lemma_longer_string_larger_value(s1@, s2@);
    }
    1
}
// </vc-code>

fn main() {}
}