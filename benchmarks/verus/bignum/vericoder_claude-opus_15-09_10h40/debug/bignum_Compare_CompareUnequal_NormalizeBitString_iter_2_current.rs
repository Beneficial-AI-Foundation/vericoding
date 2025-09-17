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

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@),
   t@.len() > 0,
   t@.len() > 1 ==> t@[0] != '0',
   ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
{/* code modified by LLM (iteration 2): Fixed type error by casting i to int */
    let mut result = Vec::new();
    let mut i = 0;
    let mut found_non_zero = false;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            ValidBitString(s@) ==> ValidBitString(result@),
            ValidBitString(s@) && !found_non_zero ==> forall|j: int| 0 <= j && j < i ==> s@[j] == '0',
            ValidBitString(s@) && found_non_zero ==> result@ == s@.subrange((i as int) - result.len() as int, i as int),
            ValidBitString(s@) && found_non_zero && result.len() > 0 ==> result@[0] != '0',
    {
        if s[i] == '1' {
            found_non_zero = true;
        }
        if found_non_zero {
            result.push(s[i]);
        }
        i = i + 1;
    }
    
    if result.len() == 0 {
        result.push('0');
    }
    
    proof {
        if ValidBitString(s@) {
            lemma_normalize_preserves_value(s@, result@);
        }
    }
    
    result
}
// </vc-code>

// <vc-spec>
exec fn CompareUnequal(s1: &[char], s2: &[char]) -> (res: i32)
  requires ValidBitString(s1@),
   ValidBitString(s2@),
   s1@.len() > 0,
   (s1@.len() > 1 ==> s1@[0] != '0'),
   s2@.len() > 0,
   (s2@.len() > 1 ==> s2@[0] != '0'),
   s1@.len() > s2@.len(),
  ensures Str2Int(s1@) < Str2Int(s2@) ==> res == -1,
    Str2Int(s1@) == Str2Int(s2@) ==> res == 0,
    Str2Int(s1@) > Str2Int(s2@) ==> res == 1
// </vc-spec>
// <vc-code>
{
    proof {
        lemma_longer_normalized_string_greater(s1@, s2@);
    }
    1
}
// </vc-code>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Fixed type error in pow2 function by casting (n-1) to nat */
proof fn lemma_normalize_preserves_value(s: Seq<char>, t: Seq<char>)
    requires
        ValidBitString(s),
        ValidBitString(t),
        t.len() > 0,
        (t.len() == 1 && t[0] == '0') || (t.len() > 1 ==> t[0] != '0'),
        (s.len() == 0 && t == seq!['0']) || exists|k: int| 0 <= k && k < s.len() && s[k] == '1' && t == s.subrange(k, s.len() as int) || (forall|j: int| 0 <= j && j < s.len() ==> s[j] == '0') && t == seq!['0'],
    ensures
        Str2Int(s) == Str2Int(t),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(t == seq!['0']);
        assert(Str2Int(s) == 0);
        assert(Str2Int(t) == 0);
    } else if s[0] == '0' {
        let s_rest = s.subrange(1, s.len() as int);
        assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + 0);
        lemma_leading_zero_removal(s);
        if s_rest.len() > 0 {
            lemma_normalize_preserves_value(s_rest, t);
        }
    } else {
        assert(s[0] == '1');
        assert(t == s);
    }
}

proof fn lemma_leading_zero_removal(s: Seq<char>)
    requires
        ValidBitString(s),
        s.len() > 0,
        s[0] == '0',
    ensures
        Str2Int(s) == Str2Int(s.subrange(1, s.len() as int)),
    decreases s.len(),
{
    if s.len() == 1 {
        assert(s[0] == '0');
        assert(Str2Int(s) == 0);
        assert(s.subrange(1, 1) == Seq::<char>::empty());
        assert(Str2Int(Seq::<char>::empty()) == 0);
    } else {
        let s_rest = s.subrange(1, s.len() as int);
        assert(s == seq![s[0]] + s_rest);
        lemma_str2int_decompose(s);
    }
}

proof fn lemma_str2int_decompose(s: Seq<char>)
    requires
        ValidBitString(s),
        s.len() > 1,
        s[0] == '0',
    ensures
        Str2Int(s) == Str2Int(s.subrange(1, s.len() as int)),
    decreases s.len(),
{
    let n = s.len() as int;
    if n == 2 {
        let last = if s[1] == '1' { 1nat } else { 0nat };
        assert(Str2Int(s) == 2 * Str2Int(seq![s[0]]) + last);
        assert(Str2Int(seq![s[0]]) == 0);
        assert(Str2Int(s) == last);
        assert(Str2Int(s.subrange(1, 2)) == last);
    } else {
        let s_prefix = s.subrange(0, n - 1);
        let s_rest = s.subrange(1, n);
        let s_rest_prefix = s_rest.subrange(0, s_rest.len() as int - 1);
        assert(s_prefix == seq![s[0]] + s_rest_prefix);
        lemma_str2int_decompose(s_prefix);
        assert(Str2Int(s_prefix) == Str2Int(s_rest_prefix));
        let last = if s[n - 1] == '1' { 1nat } else { 0nat };
        assert(Str2Int(s) == 2 * Str2Int(s_prefix) + last);
        assert(Str2Int(s_rest) == 2 * Str2Int(s_rest_prefix) + last);
        assert(Str2Int(s) == Str2Int(s_rest));
    }
}

proof fn lemma_longer_normalized_string_greater(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() > 0,
        s1.len() > 1 ==> s1[0] != '0',
        s2.len() > 0,
        s2.len() > 1 ==> s2[0] != '0',
        s1.len() > s2.len(),
    ensures
        Str2Int(s1) > Str2Int(s2),
    decreases s1.len(),
{
    if s2.len() == 1 {
        if s2[0] == '0' {
            assert(Str2Int(s2) == 0);
            lemma_positive_string(s1);
        } else {
            assert(s2[0] == '1');
            assert(Str2Int(s2) == 1);
            lemma_string_ge_2(s1);
        }
    } else {
        lemma_string_bounds(s1);
        lemma_string_bounds(s2);
    }
}

proof fn lemma_positive_string(s: Seq<char>)
    requires
        ValidBitString(s),
        s.len() > 0,
        s.len() > 1 ==> s[0] != '0',
    ensures
        Str2Int(s) >= 1,
    decreases s.len(),
{
    if s.len() == 1 {
        if s[0] == '0' {
            assert(Str2Int(s) == 0);
        } else {
            assert(s[0] == '1');
            assert(Str2Int(s) == 1);
        }
    } else {
        assert(s[0] == '1');
        let prefix = s.subrange(0, s.len() as int - 1);
        let last = if s[s.len() as int - 1] == '1' { 1nat } else { 0nat };
        assert(Str2Int(s) == 2 * Str2Int(prefix) + last);
        assert(Str2Int(prefix) >= 1);
        assert(Str2Int(s) >= 2);
    }
}

proof fn lemma_string_ge_2(s: Seq<char>)
    requires
        ValidBitString(s),
        s.len() > 1,
        s[0] != '0',
    ensures
        Str2Int(s) >= 2,
    decreases s.len(),
{
    assert(s[0] == '1');
    let prefix = s.subrange(0, s.len() as int - 1);
    let last = if s[s.len() as int - 1] == '1' { 1nat } else { 0nat };
    assert(Str2Int(s) == 2 * Str2Int(prefix) + last);
    lemma_positive_string(prefix);
    assert(Str2Int(prefix) >= 1);
    assert(Str2Int(s) >= 2);
}

proof fn lemma_string_bounds(s: Seq<char>)
    requires
        ValidBitString(s),
        s.len() > 0,
        s[0] == '1',
    ensures
        Str2Int(s) >= pow2((s.len() - 1) as nat),
        Str2Int(s) < pow2(s.len() as nat),
    decreases s.len(),
{
    if s.len() == 1 {
        assert(Str2Int(s) == 1);
        assert(pow2(0) == 1);
        assert(pow2(1) == 2);
    } else {
        let prefix = s.subrange(0, s.len() as int - 1);
        let last = if s[s.len() as int - 1] == '1' { 1nat } else { 0nat };
        assert(Str2Int(s) == 2 * Str2Int(prefix) + last);
        
        if prefix.len() == 1 {
            assert(prefix[0] == '1');
            assert(Str2Int(prefix) == 1);
            assert(Str2Int(s) >= 2 * 1 + 0);
            assert(Str2Int(s) <= 2 * 1 + 1);
            assert(pow2(1) == 2);
            assert(pow2(2) == 4);
        } else {
            lemma_string_bounds(prefix);
            assert(Str2Int(prefix) >= pow2((prefix.len() - 1) as nat));
            assert(Str2Int(prefix) < pow2(prefix.len() as nat));
            assert(Str2Int(s) >= 2 * pow2((prefix.len() - 1) as nat));
            assert(Str2Int(s) < 2 * pow2(prefix.len() as nat) + 2);
            lemma_pow2_properties((prefix.len() - 1) as nat);
            lemma_pow2_properties(prefix.len() as nat);
        }
    }
}

spec fn pow2(n: nat) -> nat
    decreases n,
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

proof fn lemma_pow2_properties(n: nat)
    ensures
        pow2(n + 1) == 2 * pow2(n),
{
    assert(pow2(n + 1) == 2 * pow2(n));
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
    let t1 = NormalizeBitString(s1);
    let t2 = NormalizeBitString(s2);
    
    if t1.len() < t2.len() {
        proof {
            lemma_longer_normalized_string_greater(t2@, t1@);
        }
        return -1;
    } else if t1.len() > t2.len() {
        proof {
            lemma_longer_normalized_string_greater(t1@, t2@);
        }
        return 1;
    } else {
        return CompareEqual(&t1, &t2);
    }
}

exec fn CompareEqual(s1: &[char], s2: &[char]) -> (res: i32)
    requires
        ValidBitString(s1@),
        ValidBitString(s2@),
        s1@.len() == s2@.len(),
        s1@.len() > 0,
        s1@.len() > 1 ==> s1@[0] != '0',
        s2@.len() > 1 ==> s2@[0] != '0',
    ensures
        Str2Int(s1@) < Str2Int(s2@) ==> res == -1,
        Str2Int(s1@) == Str2Int(s2@) ==> res == 0,
        Str2Int(s1@) > Str2Int(s2@) ==> res == 1,
{
    let mut i = 0;
    while i < s1.len()
        invariant
            0 <= i <= s1.len(),
            s1@.len() == s2@.len(),
            forall|j: int| 0 <= j && j < i ==> s1@[j] == s2@[j],
    {
        if s1[i] != s2[i] {
            if s1[i] == '0' {
                proof {
                    lemma_compare_at_position(s1@, s2@, i as int);
                }
                return -1;
            } else {
                proof {
                    lemma_compare_at_position(s1@, s2@, i as int);
                }
                return 1;
            }
        }
        i = i + 1;
    }
    
    proof {
        lemma_equal_strings(s1@, s2@);
    }
    0
}

proof fn lemma_compare_at_position(s1: Seq<char>, s2: Seq<char>, pos: int)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() == s2.len(),
        0 <= pos < s1.len(),
        forall|j: int| 0 <= j && j < pos ==> s1[j] == s2[j],
        s1[pos] != s2[pos],
    ensures
        s1[pos] == '0' && s2[pos] == '1' ==> Str2Int(s1) < Str2Int(s2),
        s1[pos] == '1' && s2[pos] == '0' ==> Str2Int(s1) > Str2Int(s2),
    decreases s1.len(),
{
    if s1.len() == 1 {
        assert(pos == 0);
        if s1[0] == '0' {
            assert(s2[0] == '1');
            assert(Str2Int(s1) == 0);
            assert(Str2Int(s2) == 1);
        } else {
            assert(s1[0] == '1');
            assert(s2[0] == '0');
            assert(Str2Int(s1) == 1);
            assert(Str2Int(s2) == 0);
        }
    } else {
        let s1_prefix = s1.subrange(0, s1.len() as int - 1);
        let s2_prefix = s2.subrange(0, s2.len() as int - 1);
        let s1_last = if s1[s1.len() as int - 1] == '1' { 1nat } else { 0nat };
        let s2_last = if s2[s2.len() as int - 1] == '1' { 1nat } else { 0nat };
        
        if pos == s1.len() as int - 1 {
            assert(forall|j: int| 0 <= j && j < s1_prefix.len() ==> s1_prefix[j] == s2_prefix[j]);
            lemma_equal_strings(s1_prefix, s2_prefix);
            assert(Str2Int(s1_prefix) == Str2Int(s2_prefix));
            assert(Str2Int(s1) == 2 * Str2Int(s1_prefix) + s1_last);
            assert(Str2Int(s2) == 2 * Str2Int(s2_prefix) + s2_last);
            if s1[pos] == '0' {
                assert(s1_last == 0);
                assert(s2_last == 1);
                assert(Str2Int(s1) < Str2Int(s2));
            } else {
                assert(s1_last == 1);
                assert(s2_last == 0);
                assert(Str2Int(s1) > Str2Int(s2));
            }
        } else {
            assert(forall|j: int| 0 <= j && j < pos ==> s1_prefix[j] == s2_prefix[j]);
            assert(s1_prefix[pos] != s2_prefix[pos]);
            lemma_compare_at_position(s1_prefix, s2_prefix, pos);
            assert(Str2Int(s1) == 2 * Str2Int(s1_prefix) + s1_last);
            assert(Str2Int(s2) == 2 * Str2Int(s2_prefix) + s2_last);
            if s1[pos] == '0' {
                assert(Str2Int(s1_prefix) < Str2Int(s2_prefix));
                assert(Str2Int(s1) < Str2Int(s2));
            } else {
                assert(Str2Int(s1_prefix) > Str2Int(s2_prefix));
                assert(Str2Int(s1) > Str2Int(s2));
            }
        }
    }
}

proof fn lemma_equal_strings(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() == s2.len(),
        forall|j: int| 0 <= j && j < s1.len() ==> s1[j] == s2[j],
    ensures
        Str2Int(s1) == Str2Int(s2),
    decreases s1.len(),
{
    if s1.len() == 0 {
        assert(Str2Int(s1) == 0);
        assert(Str2Int(s2) == 0);
    } else {
        let s1_prefix = s1.subrange(0, s1.len() as int - 1);
        let s2_prefix = s2.subrange(0, s2.len() as int - 1);
        assert(forall|j: int| 0 <= j && j < s1_prefix.len() ==> s1_prefix[j] == s2_prefix[j]);
        lemma_equal_strings(s1_prefix, s2_prefix);
        assert(s1[s1.len() as int - 1] == s2[s2.len() as int - 1]);
        let last = if s1[s1.len() as int - 1] == '1' { 1nat } else { 0nat };
        assert(Str2Int(s1) == 2 * Str2Int(s1_prefix) + last);
        assert(Str2Int(s2) == 2 * Str2Int(s2_prefix) + last);
    }
}
// </vc-code>

fn main() {}
}


