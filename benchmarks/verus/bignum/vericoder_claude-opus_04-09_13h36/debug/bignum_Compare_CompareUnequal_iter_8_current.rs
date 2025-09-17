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
    if s.len() == 0 {
        // This case can't happen given preconditions
        assert(false);
    } else if s.len() == 1 {
        assert(k == 0);
        assert(s.subrange(0, 1) =~= s);
    } else {
        // s.len() > 1
        let last_bit = if s[s.len() - 1] == '1' { 1nat } else { 0nat };
        let s_prefix = s.subrange(0, s.len() as int - 1);
        
        assert(Str2Int(s) == 2 * Str2Int(s_prefix) + last_bit);
        
        if k == 0 {
            assert(s.subrange(0, s.len() as int) =~= s);
        } else {
            // k > 0, so s[0] == '0'
            assert(s[0] == '0');
            assert(ValidBitString(s_prefix));
            
            // All elements before k in s_prefix are '0'
            assert(forall|j: int| 0 <= j && j < k && j < s_prefix.len() ==> 
                   #[trigger] s_prefix[j] == s[j] && s[j] == '0');
            
            if k == s.len() - 1 {
                // All elements except the last are '0'
                lemma_str2int_leading_zeros(s, k);
                assert(Str2Int(s.subrange(0, k)) == 0nat);
                
                // s_prefix consists of all zeros
                assert(s_prefix.len() == k);
                assert(forall|j: int| 0 <= j && j < s_prefix.len() ==> s_prefix[j] == '0');
                lemma_str2int_leading_zeros(s_prefix, s_prefix.len() as int);
                assert(Str2Int(s_prefix) == 0nat);
                
                assert(Str2Int(s) == 2 * 0 + last_bit == last_bit);
                
                // s.subrange(k, s.len()) is just the last element
                let suffix = s.subrange(k, s.len() as int);
                assert(suffix.len() == 1);
                assert(suffix[0] == s[s.len() - 1]);
                assert(Str2Int(suffix) == last_bit);
            } else {
                // k < s.len() - 1
                assert(k < s_prefix.len());
                
                // Apply lemma recursively
                lemma_str2int_suffix_after_zeros(s_prefix, k);
                assert(Str2Int(s_prefix) == Str2Int(s_prefix.subrange(k, s_prefix.len() as int)));
                
                // s_prefix.subrange(k, s_prefix.len()) == s.subrange(k, s.len() - 1)
                assert(s_prefix.subrange(k, s_prefix.len() as int) =~= s.subrange(k, s.len() as int - 1));
                
                // Calculate Str2Int(s.subrange(k, s.len()))
                let suffix = s.subrange(k, s.len() as int);
                assert(suffix[suffix.len() - 1] == s[s.len() - 1]);
                assert(suffix.subrange(0, suffix.len() as int - 1) =~= s.subrange(k, s.len() as int - 1));
                assert(Str2Int(suffix) == 2 * Str2Int(suffix.subrange(0, suffix.len() as int - 1)) + last_bit);
                assert(Str2Int(suffix) == 2 * Str2Int(s.subrange(k, s.len() as int - 1)) + last_bit);
                
                // Combine everything
                assert(Str2Int(s) == 2 * Str2Int(s_prefix) + last_bit);
                assert(Str2Int(s) == 2 * Str2Int(s.subrange(k, s.len() as int - 1)) + last_bit);
                assert(Str2Int(s) == Str2Int(suffix));
            }
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
    let mut first_one_index: usize = 0;
    
    for i in 0..s.len()
        invariant
            ValidBitString(result@),
            found_one ==> (result@.len() > 0 && result@[0] == '1'),
            !found_one ==> result@.len() == 0,
            ValidBitString(s@) ==> ValidBitString(s@.subrange(0, i as int)),
            ValidBitString(s@) && found_one ==> first_one_index < i,
            ValidBitString(s@) && found_one ==> s@[first_one_index as int] == '1',
            ValidBitString(s@) && found_one ==> (forall|j: int| 0 <= j && j < first_one_index as int ==> s@[j] == '0'),
            ValidBitString(s@) && found_one ==> 
                Str2Int(s@.subrange(first_one_index as int, i as int)) == Str2Int(result@),
            ValidBitString(s@) && !found_one ==> 
                (forall|j: int| 0 <= j && j < i as int ==> s@[j] == '0'),
            ValidBitString(s@) && !found_one ==> 
                Str2Int(s@.subrange(0, i as int)) == 0nat,
    {
        if s[i] == '1' {
            if !found_one {
                found_one = true;
                first_one_index = i;
                result.push('1');
                proof {
                    if ValidBitString(s@) {
                        assert(s@.subrange(i as int, i as int + 1).len() == 1);
                        assert(s@.subrange(i as int, i as int + 1)[0] == '1');
                        assert(Str2Int(s@.subrange(i as int, i as int + 1)) == 1nat);
                        assert(result@.len() == 1);
                        assert(result@[0] == '1');
                        assert(Str2Int(result@) == 1nat);
                    }
                }
            } else {
                proof {
                    if ValidBitString(s@) {
                        let old_result = result@;
                        let sub_prev = s@.subrange(first_one_index as int, i as int);
                        let sub_next = s@.subrange(first_one_index as int, i as int + 1);
                        assert(sub_next[sub_next.len() - 1] == '1');
                        assert(sub_next.subrange(0, sub_next.len() as int - 1) =~= sub_prev);
                        assert(Str2Int(sub_next) == 2 * Str2Int(sub_prev) + 1);
                        lemma_str2int_append_bit(old_result, '1');
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
                        let sub_prev = s@.subrange(first_one_index as int, i as int);
                        let sub_next = s@.subrange(first_one_index as int, i as int + 1);
                        assert(sub_next[sub_next.len() - 1] == '0');
                        assert(sub_next.subrange(0, sub_next.len() as int - 1) =~= sub_prev);
                        assert(Str2Int(sub_next) == 2 * Str2Int(sub_prev) + 0);
                        lemma_str2int_append_bit(old_result, '0');
                        assert(Str2Int(old_result.push('0')) == 2 * Str2Int(old_result) + 0);
                    }
                }
                result.push('0');
            } else {
                proof {
                    if ValidBitString(s@) {
                        assert(s@[i as int] == '0');
                        assert(forall|j: int| 0 <= j && j < i as int + 1 ==> s@[j] == '0');
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
                assert(first_one_index < s@.len());
                assert(forall|j: int| 0 <= j && j < first_one_index as int ==> s@[j] == '0');
                lemma_str2int_suffix_after_zeros(s@, first_one_index as int);
                assert(Str2Int(s@) == Str2Int(s@.subrange(first_one_index as int, s@.len() as int)));
                assert(Str2Int(s@.subrange(first_one_index as int, s@.len() as int)) == Str2Int(result@));
                assert(Str2Int(s@) == Str2Int(result@));
            } else {
                assert(result@.len() == 1 && result@[0] == '0');
                lemma_normalize_preserves_value(s@);
                assert(Str2Int(s@) == 0nat);
                assert(Str2Int(result@) == 0nat);
            }
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}