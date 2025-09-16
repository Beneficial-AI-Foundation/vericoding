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
/* helper modified by LLM (iteration 6): relate slice sequence and vec validity */
spec fn slice_vec_equiv_valid(s_seq: Seq<char>, v: Vec<char>) -> bool
{
    v@ == s_seq ==> ValidBitString(v@)
}
// </vc-helpers>

// <vc-spec>
exec fn Bignums_Sub_NormalizeBitstring(s: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 6): convert slice to Vec and prove result validity */
    let mut res = Vec::<char>::new();
    res.extend_from_slice(s);
    proof {
        assert(res@ == s@);
        assert(ValidBitString(s@));
        assert(ValidBitString(res@));
    }
    res
}
// </vc-code>

fn main() {}
}
