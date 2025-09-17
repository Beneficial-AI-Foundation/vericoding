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
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@), t@.len() > 0, (t@.len() > 1 ==> t@[0] != '0'), ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 7): fixed loop invariants and added proof assertions */
    let mut result = Vec::<char>::new();
    
    if s.len() == 0 {
        result.push('0');
        return result;
    }
    
    // Find first non-zero index
    let mut start_idx: usize = 0;
    let mut found_non_zero = false;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            !found_non_zero ==> forall |j: int| 0 <= j && j < i ==> s@[j] == '0' || s@[j] != '0' && s@[j] != '1',
            found_non_zero ==> start_idx < s.len() && s@[start_idx as int] != '0',
            found_non_zero ==> start_idx <= i,
        decreases s.len() - i
    {
        if s[i] != '0' {
            if !found_non_zero {
                start_idx = i;
                found_non_zero = true;
            }
        }
        i = i + 1;
    }
    
    if !found_non_zero {
        // All zeros
        result.push('0');
    } else {
        // Copy from start_idx to end
        let mut j: usize = start_idx;
        while j < s.len()
            invariant
                start_idx <= j <= s.len(),
                result@.len() == j - start_idx,
                forall |k: int| 0 <= k && k < result@.len() ==> result@[k] == s@[start_idx as int + k],
                result@.len() > 0 ==> result@[0] == s@[start_idx as int],
                result@.len() > 0 && s@[start_idx as int] != '0' ==> result@[0] != '0',
            decreases s.len() - j
        {
            result.push(s[j]);
            j = j + 1;
        }
    }
    
    // Ensure ValidBitString for result
    proof {
        if ValidBitString(s@) {
            assert forall |k: int| 0 <= k && k < result@.len() implies
                (result@[k] == '0' || result@[k] == '1') by {
                if !found_non_zero {
                    assert(result@.len() == 1);
                    assert(result@[0] == '0');
                } else {
                    assert(result@[k] == s@[start_idx as int + k]);
                    assert(s@[start_idx as int + k] == '0' || s@[start_idx as int + k] == '1');
                }
            }
            assert(ValidBitString(result@));
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}


