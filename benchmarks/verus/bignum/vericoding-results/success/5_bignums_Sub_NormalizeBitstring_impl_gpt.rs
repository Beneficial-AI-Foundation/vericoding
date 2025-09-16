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
spec fn is_bit(c: char) -> bool { c == '0' || c == '1' }
// </vc-helpers>

// <vc-spec>
exec fn Bignums_Sub_NormalizeBitstring(s: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    let mut res: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            res@.len() == i as int,
            forall |k: int| 0 <= k && k < i as int ==> res@[k] == s@[k],
        decreases s.len() - i
    {
        let c = s[i];
        res.push(c);
        i = i + 1;
    }
    res
}
// </vc-code>

fn main() {}
}
