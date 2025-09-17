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
/* helper modified by LLM (iteration 2): added decreases clause to fix compilation error */
exec fn normalize_helper(s: &[char], start_idx: usize) -> (res: Vec<char>)
    requires
        ValidBitString(s@),
        start_idx <= s@.len(),
    ensures
        ValidBitString(res@),
        res@.len() <= s@.len() - start_idx,
{
    let mut result = Vec::new();
    let mut found_one = false;
    let mut i = start_idx;
    
    while i < s.len()
        invariant
            start_idx <= i,
            i <= s@.len(),
            ValidBitString(s@),
            ValidBitString(result@),
            !found_one ==> (forall |j: int| start_idx <= j < i ==> s@[j] == '0'),
        decreases s@.len() - i
    {
        if s[i] == '1' {
            found_one = true;
        }
        if found_one {
            result.push(s[i]);
        }
        i += 1;
    }
    
    if result.len() == 0 {
        result.push('0');
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
exec fn Bignums_Sub_NormalizeBitstring(s: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to fix compilation error */
    let mut result = Vec::new();
    let mut start_idx = 0;
    
    while start_idx < s.len() && s[start_idx] == '0'
        invariant
            start_idx <= s@.len(),
            ValidBitString(s@),
            forall |j: int| 0 <= j < start_idx ==> s@[j] == '0',
        decreases s@.len() - start_idx
    {
        start_idx += 1;
    }
    
    if start_idx == s.len() {
        result.push('0');
    } else {
        let mut i = start_idx;
        while i < s.len()
            invariant
                start_idx <= i,
                i <= s@.len(),
                ValidBitString(s@),
                ValidBitString(result@),
                result@.len() == i - start_idx,
                forall |j: int| 0 <= j < result@.len() ==> result@[j] == s@[start_idx + j],
            decreases s@.len() - i
        {
            result.push(s[i]);
            i += 1;
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}
