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
proof fn lemma_str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{
}

proof fn lemma_str2int_subrange_preserved(s: Seq<char>, start: int, end: int)
    requires ValidBitString(s),
             0 <= start <= end <= s.len(),
             ValidBitString(s.subrange(start, end))
    ensures Str2Int(s.subrange(start, end)) == Str2Int(s.subrange(start, end))
{
}

proof fn lemma_valid_bit_string_subrange(s: Seq<char>, start: int, end: int)
    requires ValidBitString(s),
             0 <= start <= end <= s.len()
    ensures ValidBitString(s.subrange(start, end))
{
}

proof fn lemma_str2int_leading_zeros(s: Seq<char>)
    requires ValidBitString(s),
             s.len() > 0,
             s[0] == '0'
    ensures Str2Int(s) == Str2Int(s.subrange(1, s.len() as int))
    decreases s.len()
{
    if s.len() == 1 {
        assert(s.subrange(1, 1).len() == 0);
        assert(Str2Int(s.subrange(1, 1)) == 0);
        assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, 0)) + 0);
        assert(s.subrange(0, 0).len() == 0);
        assert(Str2Int(s.subrange(0, 0)) == 0);
        assert(Str2Int(s) == 0);
    } else {
        lemma_valid_bit_string_subrange(s, 1, s.len() as int);
        let s_prefix = s.subrange(0, s.len() as int - 1);
        lemma_valid_bit_string_subrange(s, 0, s.len() as int - 1);
        
        if s_prefix.len() > 0 && s_prefix[0] == '0' {
            lemma_str2int_leading_zeros(s_prefix);
        }
        
        let s_suffix = s.subrange(1, s.len() as int);
        let s_suffix_prefix = s_suffix.subrange(0, s_suffix.len() as int - 1);
        assert(s_suffix_prefix == s.subrange(1, s.len() as int - 1));
        assert(s_prefix.subrange(1, s_prefix.len() as int) == s.subrange(1, s.len() as int - 1));
    }
}

proof fn lemma_str2int_remove_leading_zeros(s: Seq<char>, k: int)
    requires ValidBitString(s),
             0 <= k <= s.len(),
             forall |i: int| 0 <= i < k ==> s[i] == '0'
    ensures Str2Int(s) == Str2Int(s.subrange(k, s.len() as int))
    decreases k
{
    if k == 0 {
        assert(s.subrange(0, s.len() as int) == s);
    } else if k == s.len() {
        assert(s.subrange(k, s.len() as int).len() == 0);
        assert(Str2Int(s.subrange(k, s.len() as int)) == 0);
        lemma_str2int_all_zeros(s);
    } else {
        assert(s[0] == '0');
        lemma_str2int_leading_zeros(s);
        let s_tail = s.subrange(1, s.len() as int);
        lemma_valid_bit_string_subrange(s, 1, s.len() as int);
        assert(forall |i: int| 0 <= i < k - 1 ==> s_tail[i] == '0');
        lemma_str2int_remove_leading_zeros(s_tail, k - 1);
        assert(s_tail.subrange(k - 1, s_tail.len() as int) == s.subrange(k, s.len() as int));
    }
}

proof fn lemma_str2int_all_zeros(s: Seq<char>)
    requires ValidBitString(s),
             forall |i: int| 0 <= i < s.len() ==> s[i] == '0'
    ensures Str2Int(s) == 0
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_valid_bit_string_subrange(s, 0, s.len() as int - 1);
        lemma_str2int_all_zeros(s.subrange(0, s.len() as int - 1));
    }
}

proof fn lemma_normalize_char_creates_valid_bit(c: char) -> (result: char)
    ensures result == '0' || result == '1',
            ValidBitString(seq![result])
{
    if c == '1' { '1' } else { '0' }
}

proof fn lemma_str2int_zero_is_zero()
    ensures Str2Int(seq!['0']) == 0
{
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
    let mut result = Vec::new();
    
    // Handle empty input
    if s.len() == 0 {
        result.push('0');
        proof {
            lemma_str2int_zero_is_zero();
        }
        return result;
    }
    
    // First pass: normalize all characters to valid bit chars and find first non-zero
    let mut normalized = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant 
            i <= s.len(),
            normalized@.len() == i,
            ValidBitString(normalized@),
            forall |j: int| 0 <= j < i ==> (normalized@[j] == '0' || normalized@[j] == '1'),
        decreases s.len() - i
    {
        let normalized_char = if s[i] == '1' { '1' } else { '0' };
        normalized.push(normalized_char);
        i += 1;
    }
    
    // Find first non-zero character in normalized string
    let mut start_idx = 0;
    while start_idx < normalized.len() && normalized[start_idx] == '0'
        invariant 
            start_idx <= normalized.len(),
            forall |j: int| 0 <= j < start_idx ==> normalized@[j] == '0',
            ValidBitString(normalized@)
        decreases normalized.len() - start_idx
    {
        start_idx += 1;
    }
    
    // If all characters are '0', return "0"
    if start_idx == normalized.len() {
        result.push('0');
        proof {
            assert(forall |j: int| 0 <= j < normalized@.len() ==> normalized@[j] == '0');
            lemma_str2int_all_zeros(normalized@);
            lemma_str2int_zero_is_zero();
            if ValidBitString(s@) {
                // If input was valid, normalized preserves the value
                assert(forall |j: int| 0 <= j < s@.len() ==> (s@[j] == '0' || s@[j] == '1'));
                assert(forall |j: int| 0 <= j < s@.len() ==> s@[j] == '0');
                lemma_str2int_all_zeros(s@);
            }
        }
        return result;
    }
    
    // Copy non-leading-zero part
    let mut i = start_idx;
    while i < normalized.len()
        invariant 
            start_idx <= i <= normalized.len(),
            start_idx < normalized.len(),
            result@.len() == (i - start_idx),
            ValidBitString(result@),
            ValidBitString(normalized@),
            forall |j: int| 0 <= j < result@.len() ==> result@[j] == normalized@[start_idx + j],
        decreases normalized.len() - i
    {
        result.push(normalized[i]);
        i += 1;
    }
    
    proof {
        assert(result@.len() > 0);
        if result@.len() > 1 {
            assert(result@[0] == normalized@[start_idx as int]);
            assert(normalized@[start_idx as int] != '0');
        }
        
        if ValidBitString(s@) {
            // When input is valid, normalized == s
            assert(normalized@ == s@);
            lemma_valid_bit_string_subrange(s@, start_idx as int, s@.len() as int);
            assert(result@ == s@.subrange(start_idx as int, s@.len() as int));
            lemma_str2int_remove_leading_zeros(s@, start_idx as int);
            assert(Str2Int(s@) == Str2Int(result@));
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}