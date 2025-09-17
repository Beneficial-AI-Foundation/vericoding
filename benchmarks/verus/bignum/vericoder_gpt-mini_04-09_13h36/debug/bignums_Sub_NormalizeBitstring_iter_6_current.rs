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
use vstd::prelude::*;
// </vc-helpers>

// <vc-spec>
exec fn Bignums_Sub_NormalizeBitstring(s: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
  let mut v = Vec::<char>::new();
  let mut i: int = 0;
  while i < (s@).len() as int
    invariant 0 <= i && i <= (s@).len() as int;
    invariant (v@).len() as int == i;
    invariant forall |k: int| 0 <= k && k < (v@).len() as int ==>
      (((v@).index(k) == '0') || ((v@).index(k) == '1'));
    invariant forall |k: int| 0 <= k && k < i ==>
      ((v@).index(k) == (s@).index(k));
  {
    if (s@).index(i) == '1' {
      v.push('1');
      proof {
        assert((v@).len() as int == i + 1);
        assert((v@).index(i) == '1');
        assert((s@).index(i) == '1');
        assert((v@).index(i) == (s@).index(i));
      }
    } else {
      v.push('0');
      proof {
        assert((v@).len() as int == i + 1);
        assert((v@).index(i) == '0');
        assert(((s@).index(i) == '0') || ((s@).index(i) == '1'));
        assert((s@).index(i) != '1');
        assert((s@).index(i) == '0');
        assert((v@).index(i) == (s@).index(i));
      }
    }

    i += 1;
  }

  return v;
}
// </vc-code>

fn main() {}
}