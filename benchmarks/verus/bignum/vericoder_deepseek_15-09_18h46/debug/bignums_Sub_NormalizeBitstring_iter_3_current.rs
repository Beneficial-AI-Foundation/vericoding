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
/* helper modified by LLM (iteration 3): Remove unsupported Vec::is_empty usage and add range helpers */
fn is_zero(s: &[char]) -> (res: bool)
    requires ValidBitString(s@)
    ensures res == (Str2Int(s@) == 0)
{
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i,
            i <= s.len(),
            forall |j: int| 0 <= j && j < i ==> s@[j] == '0'
    {
        if s[i] != '0' {
            return false;
        }
        i += 1;
    }
    true
}

spec fn vec_len<T>(v: Vec<T>) -> nat
    decreases v
{
    v.len() as nat
}

proof fn lemma_vec_empty<T>(v: Vec<T>)
    ensures v.len() == 0 <==> v@.len() == 0
{
}
// </vc-helpers>

// <vc-spec>
exec fn Bignums_Sub_NormalizeBitstring(s: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed compilation error by avoiding Vec::is_empty */
{
    let mut result = Vec::new();
    let mut leading_zeros_skipped = false;
    
    for i in 0..s.len() {
        if !leading_zeros_skipped && s[i] == '0' {
            continue;
        }
        leading_zeros_skipped = true;
        result.push(s[i]);
    }
    
    if vec_len(result) == 0 {
        result.push('0');
    }
    
    result
}
// </vc-code>

fn main() {}
}
