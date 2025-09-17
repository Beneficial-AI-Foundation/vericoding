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
  let mut i: nat = 0;
  while i < (s@).len() as nat
    invariant {
      i <= (s@).len() as nat;
      (v@).len() as int == i as int;
      forall |k: int| 0 <= k && k < (v@).len() as int ==>
        (((v@).index(k) == '0') || ((v@).index(k) == '1'));
      forall |k: int| 0 <= k && k < i as int ==>
        ((v@).index(k) == (s@).index(k));
    }
    decreases ((s@).len() as nat) - i
  {
    if (s@).index(i as int) == '1' {
      v.push('1');
      proof {
        assert((v@).len() as int == i as int + 1);
        assert((v@).index(i as int) == '1');
        assert((s@).index(i as int) == '1');
        assert((v@).index(i as int) == (s@).index(i as int));
      }
    } else {
      v.push('0');
      proof {
        assert((v@).len() as int == i as int + 1);
        assert((v@).index(i as int) == '0');
        // From the precondition ValidBitString(s@) and i < s.len we know s@.index(i) is '0' or '1'
        assert(((s@).index(i as int) == '0') || ((s@).index(i as int) == '1'));
        // And since we're in the else branch, it's not '1'
        assert((s@).index(i as int) != '1');
        assert((s@).index(i as int) == '0');
        assert((v@).index(i as int) == (s@).index(i as int));
      }
    }

    i = i + 1;
  }

  v
}
// </vc-code>

fn main() {}
}