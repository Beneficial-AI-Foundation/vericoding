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
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
proof fn lemma_str2int_empty_leading_zeros(s: Seq<char>)
    requires ValidBitString(s), s.len() > 0, s[0] == '0'
    ensures Str2Int(s) == Str2Int(s.subrange(1, s.len() as int))
    decreases s.len()
{
    if s.len() == 1 {
        assert(s.subrange(1, 1) == Seq::<char>::empty());
        assert(Str2Int(s.subrange(1, 1)) == 0);
        assert(Str2Int(s) == 0);
    } else {
        let s_prefix = s.subrange(0, s.len() as int - 1);
        let s_suffix = s.subrange(1, s.len() as int);
        let s_suffix_prefix = s_suffix.subrange(0, s_suffix.len() as int - 1);
        
        assert(s_prefix == s.subrange(0, s.len() as int - 1));
        assert(s_suffix_prefix == s.subrange(1, s.len() as int - 1));
        assert(s_prefix.subrange(1, s_prefix.len() as int) == s_suffix_prefix);
        
        lemma_str2int_empty_leading_zeros(s_prefix);
        
        assert(Str2Int(s_prefix) == Str2Int(s_suffix_prefix));
        assert(Str2Int(s) == 2 * Str2Int(s_prefix) + (if s[s.len() as int - 1] == '1' { 1nat } else { 0nat }));
        assert(Str2Int(s_suffix) == 2 * Str2Int(s_suffix_prefix) + (if s_suffix[s_suffix.len() as int - 1] == '1' { 1nat } else { 0nat }));
        assert(s[s.len() as int - 1] == s_suffix[s_suffix.len() as int - 1]);
    }
}

proof fn lemma_valid_bit_string_subrange(s: Seq<char>, start: int, end: int)
    requires ValidBitString(s), 0 <= start <= end <= s.len()
    ensures ValidBitString(s.subrange(start, end))
{
    assert forall |i: int| 0 <= i && i < s.subrange(start, end).len() ==> 
        s.subrange(start, end)[i] == s[start + i] && 
        (s[start + i] == '0' || s[start + i] == '1')
        by {
            if 0 <= i && i < s.subrange(start, end).len() {
                assert(s.subrange(start, end)[i] == s[start + i]);
                assert(0 <= start + i < s.len());
                assert(s[start + i] == '0' || s[start + i] == '1');
            }
        };
}
// </vc-helpers>

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@), t@.len() > 0, (t@.len() > 1 ==> t@[0] != '0'), ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    
    // Copy all characters to result
    let mut i = 0;
    while i < s.len()
        invariant 
            0 <= i <= s.len(),
            result.len() == i,
            forall |j: int| 0 <= j < i ==> result@[j] == s@[j],
            ValidBitString(result@)
    {
        result.push(s[i]);
        i += 1;
    }
    
    // Remove leading zeros
    let mut start = 0;
    while start < result.len() && result[start] == '0'
        invariant 
            0 <= start <= result.len(),
            forall |j: int| 0 <= j < start ==> result@[j] == '0',
            ValidBitString(result@)
    {
        start += 1;
    }
    
    if start == result.len() {
        // All zeros, return "0"
        let mut final_result = Vec::new();
        final_result.push('0');
        return final_result;
    }
    
    // Create result without leading zeros
    let mut final_result = Vec::new();
    let mut i = start;
    while i < result.len()
        invariant 
            start <= i <= result.len(),
            final_result.len() == i - start,
            forall |j: int| 0 <= j < i - start ==> final_result@[j] == result@[start + j],
            ValidBitString(final_result@),
            start < result.len() ==> result@[start] != '0'
    {
        final_result.push(result[i]);
        i += 1;
    }
    
    if ValidBitString(s@) {
        proof {
            lemma_valid_bit_string_subrange(result@, start as int, result.len() as int);
            assert(result@.subrange(start as int, result.len() as int) == final_result@);
            if start > 0 {
                lemma_str2int_empty_leading_zeros(result@);
            }
            assert(Str2Int(s@) == Str2Int(result@));
            assert(Str2Int(result@) == Str2Int(final_result@));
        }
    }
    
    final_result
}
// </vc-code>

fn main() {}
}