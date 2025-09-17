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
    } else {
        lemma_valid_bit_string_subrange(s, 1, s.len() as int);
        lemma_str2int_leading_zeros(s.subrange(0, s.len() as int - 1));
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
    let mut result = Vec::new();
    
    // Handle empty input
    if s.len() == 0 {
        result.push('0');
        return result;
    }
    
    // Find first non-zero character
    let mut start_idx = 0;
    while start_idx < s.len() && s[start_idx] == '0'
        invariant 
            start_idx <= s.len(),
            forall |i: int| 0 <= i < start_idx ==> s@[i] == '0'
    {
        start_idx += 1;
    }
    
    // If all characters are '0', return "0"
    if start_idx == s.len() {
        result.push('0');
        proof {
            assert(forall |i: int| 0 <= i < s@.len() ==> s@[i] == '0');
            if ValidBitString(s@) {
                lemma_str2int_leading_zeros(s@);
            }
        }
        return result;
    }
    
    // Copy non-leading-zero part
    let mut i = start_idx;
    while i < s.len()
        invariant 
            start_idx <= i <= s.len(),
            start_idx < s.len(),
            result@.len() == (i - start_idx),
            forall |j: int| 0 <= j < result@.len() ==> result@[j] == s@[start_idx + j],
            ValidBitString(result@)
    {
        result.push(s[i]);
        i += 1;
    }
    
    proof {
        assert(result@.len() > 0);
        if result@.len() > 1 {
            assert(result@[0] == s@[start_idx as int]);
            assert(s@[start_idx as int] != '0');
        }
        
        if ValidBitString(s@) {
            lemma_valid_bit_string_subrange(s@, start_idx as int, s@.len() as int);
            if start_idx > 0 {
                lemma_str2int_leading_zeros(s@);
            }
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}