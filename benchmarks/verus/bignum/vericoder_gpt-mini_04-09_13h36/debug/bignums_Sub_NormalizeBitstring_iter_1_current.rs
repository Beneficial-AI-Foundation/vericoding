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
// No helper lemmas needed.
// </vc-helpers>

// <vc-spec>
exec fn Bignums_Sub_NormalizeBitstring(s: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
  let mut v = Vec::<char>::new();
  let mut i: usize = 0;
  while i < s.len()
    invariant v.len() == i
    invariant forall |k: int| 0 <= k && k < (v@).len() as int ==>
      ((v@).index(k) == '0' || (v@).index(k) == '1')
    invariant forall |k: int| 0 <= k && k < i as int ==>
      (v@.index(k) == s@.index(k))
  {
    // push the corresponding bit from the spec-level slice view
    if s@.index(i as int) == '1' {
      v.push('1');
    } else {
      v.push('0');
    }

    // after push, prove the new element matches s@ at position i
    proof {
      // for the newly pushed index i:
      assert((v@).len() as int == i as int + 1);
      assert((v@).index(i as int) == s@.index(i as int));
      // and it is either '0' or '1' by the input precondition on s@
      assert(s@.index(i as int) == '0' || s@.index(i as int) == '1');
      // thus the invariant about bits holds for the new element as well
    }

    i += 1;
  }

  return v;
}
// </vc-code>

fn main() {}
}