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
    /* code modified by LLM (iteration 8): handle all cases properly with correct ValidBitString checks */
    let mut result = Vec::<char>::new();
    
    // Check if input is valid
    let mut is_valid = true;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            is_valid <==> forall |j: int| 0 <= j && j < i ==> (s@[j] == '0' || s@[j] == '1'),
        decreases s.len() - i
    {
        if s[i] != '0' && s[i] != '1' {
            is_valid = false;
        }
        i = i + 1;
    }
    
    if !is_valid || s.len() == 0 {
        // Invalid input or empty - return "0"
        result.push('0');
        proof {
            assert(result@.len() == 1);
            assert(result@[0] == '0');
            assert(ValidBitString(result@));
        }
        return result;
    }
    
    // Input is valid, find first non-zero
    let mut start_idx: usize = 0;
    let mut found_non_zero = false;
    let mut j: usize = 0;
    
    while j < s.len()
        invariant
            0 <= j <= s.len(),
            is_valid,
            ValidBitString(s@),
            !found_non_zero ==> forall |k: int| 0 <= k && k < j ==> s@[k] == '0',
            found_non_zero ==> start_idx < s.len() && s@[start_idx as int] == '1',
            found_non_zero ==> start_idx <= j,
        decreases s.len() - j
    {
        if s[j] == '1' {
            if !found_non_zero {
                start_idx = j;
                found_non_zero = true;
            }
        }
        j = j + 1;
    }
    
    if !found_non_zero {
        // All zeros
        result.push('0');
        proof {
            assert(result@.len() == 1);
            assert(result@[0] == '0');
            assert(ValidBitString(result@));
            assert(forall |k: int| 0 <= k && k < s@.len() ==> s@[k] == '0');
        }
    } else {
        // Copy from start_idx to end
        let mut k: usize = start_idx;
        while k < s.len()
            invariant
                start_idx <= k <= s.len(),
                ValidBitString(s@),
                result@.len() == k - start_idx,
                forall |m: int| 0 <= m && m < result@.len() ==> result@[m] == s@[start_idx as int + m],
                forall |m: int| 0 <= m && m < result@.len() ==> (result@[m] == '0' || result@[m] == '1'),
                result@.len() > 0 ==> result@[0] == s@[start_idx as int],
                s@[start_idx as int] == '1',
                result@.len() > 0 ==> result@[0] == '1',
            decreases s.len() - k
        {
            result.push(s[k]);
            k = k + 1;
        }
        
        proof {
            assert(ValidBitString(result@));
            assert(result@[0] == '1');
            assert(result@[0] != '0');
        }
    }
    
    proof {
        assert(result@.len() > 0);
        assert(ValidBitString(result@));
        if result@.len() > 1 {
            assert(result@[0] != '0');
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}


