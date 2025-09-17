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
proof fn lemma_str2int_leading_zeros(s: Seq<char>)
  requires ValidBitString(s), s.len() > 0, s[0] == '0'
  ensures Str2Int(s) == Str2Int(s.subrange(1, s.len() as int))
  decreases s.len()
{
  if s.len() == 1 {
    assert(Str2Int(s) == 0);
    assert(s.subrange(1, s.len() as int) =~= Seq::<char>::empty());
    assert(Str2Int(s.subrange(1, s.len() as int)) == 0);
  } else {
    let sub = s.subrange(0, s.len() as int - 1);
    assert(sub[0] == '0');
    lemma_str2int_leading_zeros(sub);
    assert(Str2Int(sub) == Str2Int(sub.subrange(1, sub.len() as int)));
    assert(sub.subrange(1, sub.len() as int) =~= s.subrange(1, s.len() as int - 1));
  }
}

proof fn lemma_valid_bit_string_subrange(s: Seq<char>, start: int, end: int)
  requires ValidBitString(s), 0 <= start <= end <= s.len()
  ensures ValidBitString(s.subrange(start, end))
{
}

proof fn lemma_str2int_empty()
  ensures Str2Int(Seq::<char>::empty()) == 0
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
  let mut result = Vec::<char>::new();
  
  // Handle empty input
  if s.len() == 0 {
    result.push('0');
    return result;
  }
  
  // Find first non-zero character
  let mut start: usize = 0;
  while start < s.len() && s[start] == '0'
    invariant 0 <= start <= s.len(),
             forall |i: int| 0 <= i < start ==> s[i] == '0'
  {
    start += 1;
  }
  
  // If all zeros, return "0"
  if start == s.len() {
    result.push('0');
    
    // Prove that original string was all zeros so Str2Int is 0
    proof {
      if ValidBitString(s@) {
        let mut i = s.len();
        while i > 0
          invariant 0 <= i <= s.len(),
                   forall |j: int| i <= j < s.len() ==> s[j] == '0',
                   Str2Int(s@.subrange(i as int, s.len() as int)) == 0
        {
          i -= 1usize;
          // s[i] == '0', so the recursive formula gives us 2*Str2Int(prefix) + 0
          // We need to show Str2Int of this segment is still 0
        }
      }
    }
    
    return result;
  }
  
  // Copy from first non-zero to end
  let mut i = start;
  while i < s.len()
    invariant start <= i <= s.len(),
             result.len() == i - start,
             forall |j: int| 0 <= j < result.len() ==> result[j] == s[start + j],
             start < s.len() ==> s[start as int] == '1'
  {
    result.push(s[i]);
    i += 1;
  }
  
  proof {
    if ValidBitString(s@) {
      // Prove ValidBitString(result@)
      assert(forall |j: int| 0 <= j < result.len() ==> 
        (result[j] == '0' || result[j] == '1'));
      
      // Prove result doesn't start with '0' unless single '0'
      if result.len() > 1 {
        assert(result[0] == s[start as int]);
        assert(s[start as int] == '1');
      }
      
      // Prove Str2Int equality using leading zeros lemma
      if start > 0 {
        lemma_valid_bit_string_subrange(s@, 0, s.len() as int);
        let mut k: usize = 0;
        while k < start
          invariant 0 <= k <= start,
                   Str2Int(s@) == Str2Int(s@.subrange(k as int, s.len() as int))
        {
          lemma_str2int_leading_zeros(s@.subrange(k as int, s.len() as int));
          k += 1;
        }
        assert(s@.subrange(start as int, s.len() as int) =~= result@);
      } else {
        assert(s@ =~= result@);
      }
    }
  }
  
  result
}
// </vc-code>

fn main() {}
}