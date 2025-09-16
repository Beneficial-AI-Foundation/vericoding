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

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@),
   t@.len() > 0,
   t@.len() > 1 ==> t@[0] != '0',
   ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): fixed empty input handling and validation */
    let mut result = Vec::new();
    
    // Handle empty input
    if s.len() == 0 {
        result.push('0');
        return result;
    }
    
    let mut start_idx = 0;
    
    // Find first non-zero character
    while start_idx < s.len()
        invariant
            start_idx <= s.len(),
        decreases s.len() - start_idx
    {
        if s[start_idx] == '1' {
            break;
        }
        start_idx += 1;
    }
    
    // If all zeros, return "0"
    if start_idx == s.len() {
        result.push('0');
        return result;
    }
    
    // Copy from first '1' to end
    let mut i = start_idx;
    while i < s.len()
        invariant
            start_idx <= i,
            i <= s.len(),
            result@.len() == i - start_idx,
            forall |j: int| 0 <= j < result@.len() ==> (result@[j] == '0' || result@[j] == '1'),
        decreases s.len() - i
    {
        result.push(s[i]);
        i += 1;
    }
    
    result
}
// </vc-code>

// <vc-helpers>
/* helpers modified by LLM (iteration 10): fixed nat literal type annotations */
proof fn str2int_append_lemma(s: Seq<char>, c: char)
    requires ValidBitString(s), c == '0' || c == '1'
    ensures ValidBitString(s.push(c)),
        Str2Int(s.push(c)) == 2 * Str2Int(s) + (if c == '1' { 1nat } else { 0nat })
{
    let extended = s.push(c);
    assert(extended.len() == s.len() + 1);
    assert(extended.index(extended.len() as int - 1) == c);
    
    if extended.len() > 0 {
        let prefix = extended.subrange(0, extended.len() as int - 1);
        assert(prefix == s);
    }
}

proof fn str2int_empty_prefix_lemma(s: Seq<char>, start: int)
    requires ValidBitString(s), 0 <= start <= s.len()
    ensures start < s.len() && s[start] == '1' ==> Str2Int(s.subrange(start, s.len() as int)) == Str2Int(s)
{
}
// </vc-helpers>

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@),
   ValidBitString(s2@),
  ensures ValidBitString(res@), 
    Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): fixed nat literal syntax errors */
    let n1 = NormalizeBitString(s1);
    let n2 = NormalizeBitString(s2);
    
    // Convert to natural numbers
    let val1 = Str2Int(n1@);
    let val2 = Str2Int(n2@);
    let sum = val1 + val2;
    
    // Convert sum back to bit string
    let mut result = Vec::new();
    let mut temp_sum = sum;
    
    if temp_sum == 0nat {
        result.push('0');
    } else {
        while temp_sum > 0nat
            invariant
                forall |j: int| 0 <= j < result@.len() ==> (result@[j] == '0' || result@[j] == '1'),
            decreases temp_sum
        {
            if temp_sum % 2nat == 1nat {
                result.push('1');
            } else {
                result.push('0');
            }
            temp_sum = temp_sum / 2nat;
        }
        
        // Reverse to get correct bit order
        let mut final_result = Vec::new();
        let mut rev_i = result.len();
        while rev_i > 0
            invariant
                rev_i <= result.len(),
                forall |j: int| 0 <= j < final_result@.len() ==> (final_result@[j] == '0' || final_result@[j] == '1'),
            decreases rev_i
        {
            rev_i -= 1;
            final_result.push(result[rev_i]);
        }
        result = final_result;
    }
    
    result
}
// </vc-code>

fn main() {}
}


