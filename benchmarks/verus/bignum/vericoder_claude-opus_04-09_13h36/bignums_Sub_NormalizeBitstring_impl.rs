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
    let mut result = Vec::<char>::new();
    
    for i in 0..s.len()
        invariant
            0 <= i <= s.len(),
            result.len() == i,
            forall |j: int| 0 <= j && j < i ==> result@[j] == s@[j],
            ValidBitString(s@),
            ValidBitString(result@),
    {
        let c = s[i];
        assert(s@[i as int] == '0' || s@[i as int] == '1');
        result.push(c);
    }
    
    result
}
// </vc-code>

fn main() {}
}