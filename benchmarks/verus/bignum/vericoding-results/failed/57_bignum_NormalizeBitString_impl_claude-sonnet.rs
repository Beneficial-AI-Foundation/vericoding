// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 {
    0nat
  } else {
    2nat * str2int(s.subrange(0, s.len() as int - 1)) + 
    (if s[s.len() as int - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed single character case and strengthened proof structure */
spec fn char_to_nat(c: char) -> nat {
    if c == '1' { 1nat } else { 0nat }
}

proof fn str2int_remove_leading_zeros(s: Seq<char>, i: int)
    requires
        valid_bit_string(s),
        0 <= i < s.len(),
        forall|j: int| 0 <= j < i ==> s[j] == '0'
    ensures
        str2int(s) == str2int(s.subrange(i, s.len() as int))
    decreases s.len() - i
{
    if i == 0 {
        assert(s.subrange(0, s.len() as int) =~= s);
    } else {
        let prefix = s.subrange(0, s.len() as int - 1);
        let last_char = s[s.len() as int - 1];
        
        if i < prefix.len() {
            str2int_remove_leading_zeros(prefix, i);
            
            let target_subrange = s.subrange(i, s.len() as int);
            let prefix_subrange = prefix.subrange(i, prefix.len() as int);
            
            assert(target_subrange.len() == prefix_subrange.len() + 1);
            assert(forall|k: int| 0 <= k < prefix_subrange.len() ==> 
                   target_subrange[k] == prefix_subrange[k]);
            assert(target_subrange[target_subrange.len() - 1] == last_char);
            
            assert(str2int(target_subrange) == 
                   2nat * str2int(target_subrange.subrange(0, target_subrange.len() - 1)) + 
                   char_to_nat(last_char));
            assert(target_subrange.subrange(0, target_subrange.len() - 1) =~= prefix_subrange);
            assert(str2int(target_subrange) == 2nat * str2int(prefix_subrange) + char_to_nat(last_char));
            
            assert(str2int(s) == 2nat * str2int(prefix) + char_to_nat(last_char));
            assert(str2int(prefix) == str2int(prefix_subrange));
        } else {
            assert(forall|j: int| 0 <= j < prefix.len() ==> prefix[j] == '0');
            str2int_all_zeros(prefix);
            assert(str2int(prefix) == 0nat);
            
            let single_char = s.subrange(i, s.len() as int);
            assert(single_char.len() == 1);
            assert(single_char[0] == last_char);
            
            // For single character, str2int follows the definition directly
            assert(str2int(single_char) == 2nat * str2int(single_char.subrange(0, 0)) + char_to_nat(last_char));
            assert(single_char.subrange(0, 0) =~= Seq::<char>::empty());
            assert(str2int(Seq::<char>::empty()) == 0nat);
            assert(str2int(single_char) == char_to_nat(last_char));
            
            assert(str2int(s) == 2nat * 0nat + char_to_nat(last_char));
            assert(str2int(s) == char_to_nat(last_char));
        }
    }
}

proof fn str2int_all_zeros(s: Seq<char>)
    requires
        valid_bit_string(s),
        forall|j: int| 0 <= j < s.len() ==> s[j] == '0'
    ensures
        str2int(s) == 0nat
    decreases s.len()
{
    if s.len() == 0 {
        // Base case
    } else {
        let prefix = s.subrange(0, s.len() as int - 1);
        assert(s[s.len() as int - 1] == '0');
        assert(forall|j: int| 0 <= j < prefix.len() ==> prefix[j] == '0');
        str2int_all_zeros(prefix);
        assert(str2int(s) == 2nat * 0nat + 0nat);
    }
}

proof fn str2int_empty_is_zero()
    ensures str2int(Seq::<char>::empty()) == 0nat
{
}

proof fn valid_bit_string_preserved(s: Seq<char>)
    requires valid_bit_string(s), s.len() > 0
    ensures valid_bit_string(s.subrange(1, s.len() as int))
{
    let sub = s.subrange(1, s.len() as int);
    assert(forall|i: int| 0 <= i < sub.len() ==> sub[i] == s[i + 1]);
}

proof fn str2int_preserves_value_on_correction(original: Seq<char>, corrected: Seq<char>)
    requires
        original.len() == corrected.len(),
        valid_bit_string(corrected),
        forall|i: int| 0 <= i < original.len() ==> (
            (original[i] == '0' || original[i] == '1') ==> original[i] == corrected[i]
        )
    ensures
        valid_bit_string(original) ==> str2int(original) == str2int(corrected)
    decreases original.len()
{
    if valid_bit_string(original) {
        if original.len() == 0 {
            assert(corrected.len() == 0);
        } else {
            let orig_prefix = original.subrange(0, original.len() - 1);
            let corr_prefix = corrected.subrange(0, corrected.len() - 1);
            let orig_last = original[original.len() - 1];
            let corr_last = corrected[corrected.len() - 1];
            
            assert(valid_bit_string(orig_prefix));
            assert(orig_last == corr_last);
            
            str2int_preserves_value_on_correction(orig_prefix, corr_prefix);
            
            assert(str2int(original) == 2nat * str2int(orig_prefix) + char_to_nat(orig_last));
            assert(str2int(corrected) == 2nat * str2int(corr_prefix) + char_to_nat(corr_last));
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn normalize_bit_string(s: Vec<char>) -> (t: Vec<char>)
  ensures 
    valid_bit_string(t@) &&
    t@.len() > 0 &&
    (t@.len() > 1 ==> t@[0] != '0') &&
    (valid_bit_string(s@) ==> str2int(s@) == str2int(t@))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): Fixed proof structure and invariant specifications */
    let mut result = s;
    
    // Ensure we have at least one character first
    if result.len() == 0 {
        result.push('0');
        proof {
            str2int_empty_is_zero();
        }
        return result;
    }
    
    // Store original sequence for proof - declare as ghost variable
    let ghost was_valid_originally = valid_bit_string(s@);
    let ghost original_seq = s@;
    
    // Check if input is a valid bit string - if not, make it valid
    let mut i = 0;
    while i < result.len()
        invariant
            0 <= i <= result.len(),
            forall|j: int| 0 <= j < i ==> (result[j] == '0' || result[j] == '1'),
            result.len() > 0,
            result.len() == original_seq.len(),
            forall|j: int| #![auto] 0 <= j < original_seq.len() ==> (
                (original_seq[j] == '0' || original_seq[j] == '1') ==> original_seq[j] == result[j]
            )
        decreases result.len() - i
    {
        if result[i] != '0' && result[i] != '1' {
            result.set(i, '0');
        }
        i += 1;
    }
    
    // Now result is guaranteed to be a valid bit string
    proof {
        assert(valid_bit_string(result@));
        if was_valid_originally {
            str2int_preserves_value_on_correction(original_seq, result@);
            assert(str2int(original_seq) == str2int(result@));
        }
    }
    
    // Remove leading zeros
    while result.len() > 1 && result[0] == '0'
        invariant
            valid_bit_string(result@),
            result@.len() > 0,
            was_valid_originally ==> str2int(original_seq) == str2int(result@)
        decreases result.len()
    {
        proof {
            let old_result = result@;
            valid_bit_string_preserved(old_result);
            if was_valid_originally {
                str2int_remove_leading_zeros(old_result, 1);
                assert(str2int(old_result) == str2int(old_result.subrange(1, old_result.len() as int)));
            }
        }
        result.remove(0);
    }
    
    result
}
// </vc-code>


}

fn main() {}