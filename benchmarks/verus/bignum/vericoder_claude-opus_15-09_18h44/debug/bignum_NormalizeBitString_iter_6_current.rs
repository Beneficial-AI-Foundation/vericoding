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
    /* code modified by LLM (iteration 6): added decreases clause to loops */
    let mut result = Vec::<char>::new();
    let mut start_idx: usize = 0;
    let mut found_start = false;
    
    // Find the first non-zero character
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            !found_start ==> forall |j: int| 0 <= j && j < i ==> ValidBitString(s@) ==> s@[j] == '0',
            found_start ==> start_idx < s.len() && (ValidBitString(s@) ==> s@[start_idx as int] != '0'),
            found_start ==> start_idx < i,
        decreases s.len() - i
    {
        if s[i] != '0' && !found_start {
            start_idx = i;
            found_start = true;
        }
        i = i + 1;
    }
    
    // Copy from start_idx to end
    if found_start {
        let mut j: usize = start_idx;
        while j < s.len()
            invariant
                start_idx <= j <= s.len(),
                ValidBitString(result@),
                result@.len() == j - start_idx,
                ValidBitString(s@) ==> (
                    forall |k: int| 0 <= k && k < result@.len() ==>
                        result@[k] == s@[start_idx as int + k]
                ),
                ValidBitString(s@) && result@.len() > 0 ==> result@[0] == s@[start_idx as int],
                ValidBitString(s@) && result@.len() > 0 && s@[start_idx as int] != '0' ==> result@[0] != '0',
            decreases s.len() - j
        {
            result.push(s[j]);
            j = j + 1;
        }
    } else {
        // All zeros or empty
        result.push('0');
    }
    
    result
}
// </vc-code>

fn main() {}
}


