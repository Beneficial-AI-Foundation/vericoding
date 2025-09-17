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
proof fn lemma_str2int_append_bit(s: Seq<char>, bit: char)
    requires
        ValidBitString(s),
        bit == '0' || bit == '1',
    ensures
        ValidBitString(s.push(bit)),
        Str2Int(s.push(bit)) == 2 * Str2Int(s) + (if bit == '1' { 1nat } else { 0nat }),
    decreases s.len(),
{
    let s_new = s.push(bit);
    assert(s_new.len() == s.len() + 1);
    assert(s_new.subrange(0, s_new.len() as int - 1) =~= s);
    assert(s_new.index(s_new.len() as int - 1) == bit);
}

proof fn lemma_str2int_leading_zeros(s: Seq<char>, k: int)
    requires
        ValidBitString(s),
        0 <= k <= s.len(),
        forall|j: int| 0 <= j && j < k ==> s[j] == '0',
    ensures
        Str2Int(s.subrange(0, k)) == 0nat,
    decreases k,
{
    if k == 0 {
        assert(s.subrange(0, 0).len() == 0);
        assert(Str2Int(s.subrange(0, 0)) == 0nat);
    } else {
        let sub = s.subrange(0, k);
        assert(sub.len() == k);
        assert(sub[k - 1] == s[k - 1] == '0');
        assert(sub.subrange(0, k - 1) =~= s.subrange(0, k - 1));
        lemma_str2int_leading_zeros(s, k - 1);
        assert(Str2Int(s.subrange(0, k - 1)) == 0nat);
        assert(Str2Int(sub) == 2 * Str2Int(sub.subrange(0, k - 1)) + 0);
        assert(Str2Int(sub) == 0nat);
    }
}

proof fn lemma_str2int_suffix_after_zeros(s: Seq<char>, k: int)
    requires
        ValidBitString(s),
        0 <= k < s.len(),
        forall|j: int| 0 <= j && j < k ==> s[j] == '0',
    ensures
        Str2Int(s) == Str2Int(s.subrange(k, s.len() as int)),
    decreases s.len(),
{
    if k == 0 {
        assert(s.subrange(0, s.len() as int) =~= s);
    } else {
        assert(s[0] == '0');
        assert(s.subrange(0, s.len() as int - 1).len() == s.len() - 1);
        let s_prefix = s.subrange(0, s.len() as int - 1);
        assert(ValidBitString(s_prefix));
        
        if k == s.len() - 1 {
            // Last element case
            assert(s[s.len() - 1] == '0');
            lemma_str2int_leading_zeros(s, s.len() as int);
            assert(Str2Int(s) == 0nat);
            assert(s.subrange(k, s.len() as int).len() == 1);
            assert(s.subrange(k, s.len() as int)[0] == '0');
            assert(Str2Int(s.subrange(k, s.len() as int)) == 0nat);
        } else {
            // Recursive case
            assert(forall|j: int| 0 <= j && j < k - 1 ==> #[trigger] s_prefix[j] == s[j] && s[j] == '0');
            lemma_str2int_suffix_after_zeros(s_prefix, k - 1);
            assert(Str2Int(s_prefix) == Str2Int(s_prefix.subrange(k - 1, s_prefix.len() as int)));
            assert(s_prefix.subrange(k - 1, s_prefix.len() as int) =~= s.subrange(k - 1, s.len() as int - 1));
            
            // Now handle the last digit
            let last_digit = s[s.len() - 1];
            if last_digit == '0' {
                assert(Str2Int(s) == 2 * Str2Int(s_prefix) + 0);
                assert(Str2Int(s.subrange(k, s.len() as int)) == 
                       2 * Str2Int(s.subrange(k, s.len() as int - 1)) + 0);
            } else {
                assert(last_digit == '1');
                assert(Str2Int(s) == 2 * Str2Int(s_prefix) + 1);
                assert(Str2Int(s.subrange(k, s.len() as int)) == 
                       2 * Str2Int(s.subrange(k, s.len() as int - 1)) + 1);
            }
            
            assert(Str2Int(s.subrange(k, s.len() as int - 1)) == Str2Int(s_prefix.subrange(k - 1, s_prefix.len() as int)));
            assert(Str2Int(s) == Str2Int(s.subrange(k, s.len() as int)));
        }
    }
}

proof fn lemma_normalize_preserves_value(s: Seq<char>)
    requires ValidBitString(s),
    ensures 
        s.len() == 0 ==> Str2Int(s) == 0nat,
        s.len() > 0 && (forall|j: int| 0 <= j && j < s.len() ==> s[j] == '0') ==> Str2Int(s) == 0nat,
{
    if s.len() > 0 && (forall|j: int| 0 <= j && j < s.len() ==> s[j] == '0') {
        lemma_str2int_leading_zeros(s, s.len() as int);
        assert(s.subrange(0, s.len() as int) =~= s);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@),
   t@.len() > 0,
   t@.len() > 1 ==> t@[0] != '0',
   ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::<char>::new();
    let mut found_one = false;
    
    for i in 0..s.len()
        invariant
            ValidBitString(result@),
            found_one ==> (result@.len() > 0 && result@[0] == '1'),
            !found_one ==> result@.len() == 0,
            ValidBitString(s@) ==> ValidBitString(s@.subrange(0, i as int)),
            ValidBitString(s@) && found_one ==> 
                Str2Int(s@.subrange(0, i as int)) == Str2Int(result@),
            ValidBitString(s@) && !found_one ==> 
                (forall|j: int| 0 <= j && j < i as int ==> s@[j] == '0'),
            ValidBitString(s@) && !found_one ==> 
                Str2Int(s@.subrange(0, i as int)) == 0nat,
    {
        if s[i] == '1' {
            if !found_one {
                found_one = true;
                result.push('1');
                proof {
                    if ValidBitString(s@) {
                        assert(ValidBitString(s@.subrange(0, i as int + 1)));
                        assert(forall|j: int| 0 <= j && j < i as int ==> s@[j] == '0');
                        lemma_str2int_leading_zeros(s@, i as int);
                        assert(Str2Int(s@.subrange(0, i as int)) == 0nat);
                        let sub_next = s@.subrange(0, i as int + 1);
                        assert(sub_next.index(sub_next.len() as int - 1) == '1');
                        assert(sub_next.subrange(0, sub_next.len() as int - 1) =~= s@.subrange(0, i as int));
                        assert(Str2Int(sub_next) == 2 * 0 + 1);
                        assert(Str2Int(sub_next) == 1nat);
                        assert(result@.len() == 1);
                        assert(result@[0] == '1');
                        assert(Str2Int(result@) == 1nat);
                    }
                }
            } else {
                proof {
                    if ValidBitString(s@) {
                        let old_result = result@;
                        lemma_str2int_append_bit(old_result, '1');
                        assert(ValidBitString(s@.subrange(0, i as int + 1)));
                        let sub_prev = s@.subrange(0, i as int);
                        let sub_next = s@.subrange(0, i as int + 1);
                        assert(sub_next.index(sub_next.len() as int - 1) == '1');
                        assert(sub_next.subrange(0, sub_next.len() as int - 1) =~= sub_prev);
                        assert(Str2Int(sub_next) == 2 * Str2Int(sub_prev) + 1);
                        assert(Str2Int(old_result.push('1')) == 2 * Str2Int(old_result) + 1);
                    }
                }
                result.push('1');
            }
        } else if s[i] == '0' {
            if found_one {
                proof {
                    if ValidBitString(s@) {
                        let old_result = result@;
                        lemma_str2int_append_bit(old_result, '0');
                        assert(ValidBitString(s@.subrange(0, i as int + 1)));
                        let sub_prev = s@.subrange(0, i as int);
                        let sub_next = s@.subrange(0, i as int + 1);
                        assert(sub_next.index(sub_next.len() as int - 1) == '0');
                        assert(sub_next.subrange(0, sub_next.len() as int - 1) =~= sub_prev);
                        assert(Str2Int(sub_next) == 2 * Str2Int(sub_prev) + 0);
                        assert(Str2Int(old_result.push('0')) == 2 * Str2Int(old_result) + 0);
                    }
                }
                result.push('0');
            } else {
                proof {
                    if ValidBitString(s@) {
                        assert(s@[i as int] == '0');
                        assert(forall|j: int| 0 <= j && j < i as int + 1 ==> 
                               (j < i as int ==> s@[j] == '0') && (j == i as int ==> s@[j] == '0'));
                        lemma_str2int_leading_zeros(s@, i as int + 1);
                    }
                }
            }
        }
    }
    
    if result.len() == 0 {
        result.push('0');
        proof {
            if ValidBitString(s@) {
                assert(forall|j: int| 0 <= j && j < s@.len() ==> s@[j] == '0');
                lemma_normalize_preserves_value(s@);
                assert(Str2Int(s@) == 0nat);
                assert(result@.len() == 1);
                assert(result@[0] == '0');
                assert(Str2Int(result@) == 0nat);
            }
        }
    }
    
    proof {
        if ValidBitString(s@) {
            if found_one {
                assert(Str2Int(s@) == Str2Int(result@));
            } else {
                assert(result@.len() == 1 && result@[0] == '0');
                assert(Str2Int(result@) == 0nat);
                assert(forall|j: int| 0 <= j && j < s@.len() ==> s@[j] == '0');
                lemma_normalize_preserves_value(s@);
                assert(Str2Int(s@) == 0nat);
            }
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}