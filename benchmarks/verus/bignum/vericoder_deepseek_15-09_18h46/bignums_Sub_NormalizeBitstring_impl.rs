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
/* helper modified by LLM (iteration 10): Fix exec mode call by making is_zero exec function */
exec fn is_zero(s: &[char]) -> (res: bool)
    requires ValidBitString(s@)
    ensures res == (Str2Int(s@) == 0)
{
    let mut i = 0;
    let mut all_zeros = true;
    while i < s.len()
        invariant
            0 <= i && i <= s.len(),
            all_zeros == (forall |j: int| 0 <= j && j < i ==> s[j] == '0')
        decreases s.len() - i
    {
        if s[i] != '0' {
            all_zeros = false;
        }
        i += 1;
    }
    all_zeros
}
// </vc-helpers>

// <vc-spec>
exec fn Bignums_Sub_NormalizeBitstring(s: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fix is_zero call with proper exec function */
{
    let mut result = Vec::new();
    let mut leading_zeros_skipped = false;
    
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i && i <= s.len(),
            ValidBitString(result@),
            if leading_zeros_skipped {
                Str2Int(result@ + s@.subrange(i as int, s.len() as int)) == Str2Int(s@)
            } else {
                Str2Int(result@) == 0
            },
            result.len() == 0 || !is_zero(&result)
        decreases s.len() - i
    {
        if !leading_zeros_skipped && s[i] == '0' {
            i += 1;
            continue;
        }
        leading_zeros_skipped = true;
        result.push(s[i]);
        i += 1;
    }
    
    if result.len() == 0 {
        result.push('0');
    }
    
    result
}
// </vc-code>

fn main() {}
}
