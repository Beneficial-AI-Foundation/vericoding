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
/* helper modified by LLM (iteration 2): construct Vec<char> from slice and prove equality and validity */
proof fn slice_to_vec_valid(s: &[char]) -> (v: Vec<char>)
    requires ValidBitString(s@)
    ensures
        v@ == s@,
        ValidBitString(v@),
{
    let mut v = Vec::<char>::new();
    v.extend_from_slice(s);
    proof {
        assert(v@ == s@);
        assert(ValidBitString(v@));
    }
    v
}
// </vc-helpers>

// <vc-spec>
exec fn Bignums_Sub_NormalizeBitstring(s: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): convert slice to Vec by extending and prove validity */
    let mut res = Vec::<char>::new();
    res.extend_from_slice(s);
    proof {
        let v = slice_to_vec_valid(s);
        assert(res@ == v@);
        assert(ValidBitString(res@));
    }
    res
}
// </vc-code>

fn main() {}
}
