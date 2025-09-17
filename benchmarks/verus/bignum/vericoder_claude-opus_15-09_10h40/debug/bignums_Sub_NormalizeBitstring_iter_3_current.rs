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
    /* code modified by LLM (iteration 3): Fix type error - use s@[i as int] for sequence indexing */
    let mut result = Vec::<char>::new();
    let mut found_one = false;
    
    for i in 0..s.len()
        invariant
            0 <= i <= s.len(),
            ValidBitString(s@),
            forall |j: int| 0 <= j && j < result.len() ==> (result@[j] == '0' || result@[j] == '1'),
    {
        if s[i] == '1' {
            found_one = true;
        }
        if found_one {
            assert(s@[i as int] == '0' || s@[i as int] == '1');
            result.push(s[i]);
        }
    }
    
    if result.len() == 0 {
        result.push('0');
    }
    
    result
}
// </vc-code>

fn main() {}
}
