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
spec fn is_all_zeros(s: Seq<char>) -> bool {
    forall |i: int| 0 <= i && i < s.len() ==> s.index(i) == '0'
}
// </vc-helpers>

// <vc-spec>
exec fn Bignums_Sub_NormalizeBitstring(s: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    let mut i: int = 0;
    while i < s.len() - 1
        invariant
            0 <= i,
            i <= s.len() - 1,
            ValidBitString(s@),
            forall |j: int| 0 <= j && j < i ==> s.index(j) == '0',
        decreases s.len() - i
    {
        if s.index(i) == '1' {
            break;
        }
        i = i + 1;
    }
    let mut res = Vec::<char>::new();
    let mut k = i;
    while k < s.len()
        invariant
            i <= k,
            k <= s.len(),
            ValidBitString(s@),
            res@.len() == (k - i) as nat,
            forall |idx: int| 0 <= idx && idx < k - i ==> res@[idx] == s@[i + idx],
            res@.len() >= 0,
        decreases s.len() - k
    {
        res.push(s.index(k));
        k = k + 1;
    }
    if res.len() == 0 {
        res.push('0');
    }
    res
}
// </vc-code>

fn main() {}
}
