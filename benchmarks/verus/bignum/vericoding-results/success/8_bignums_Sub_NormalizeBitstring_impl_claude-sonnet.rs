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

// </vc-helpers>

// <vc-spec>
exec fn Bignums_Sub_NormalizeBitstring(s: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    
    // Find first non-zero character
    while i < s.len()
        invariant 
            0 <= i <= s.len(),
            ValidBitString(s@),
            forall |j: int| 0 <= j < i ==> s@[j] == '0'
        decreases s.len() - i
    {
        if s[i] != '0' {
            break;
        }
        i += 1;
    }
    
    let start_index = i;
    
    // Copy remaining characters
    while i < s.len()
        invariant
            0 <= start_index <= i <= s.len(),
            ValidBitString(s@),
            ValidBitString(result@),
            result@.len() == (i - start_index) as int,
            forall |j: int| 0 <= j < result@.len() ==> result@[j] == s@[start_index + j]
        decreases s.len() - i
    {
        result.push(s[i]);
        i += 1;
    }
    
    // If result is empty, return "0"
    if result.len() == 0 {
        result.push('0');
    }
    
    proof {
        assert(ValidBitString(result@)) by {
            if result@.len() == 1 && result@[0] == '0' {
                assert(ValidBitString(result@));
            } else {
                assert(forall |j: int| 0 <= j < result@.len() ==> 
                    (result@[j] == '0' || result@[j] == '1'));
            }
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}