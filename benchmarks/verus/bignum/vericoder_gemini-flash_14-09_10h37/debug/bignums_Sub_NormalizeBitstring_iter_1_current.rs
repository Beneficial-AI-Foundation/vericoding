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
    let mut i = 0;
    while i < s.len() && s[i] == '0'
        invariant
            0 <= i && i <= s.len()
    {
        i = i + 1;
    }

    let mut res_vec = Vec::<char>::new();
    let start_index = i as int;

    if start_index == s.len() {
        res_vec.push('0');
        return res_vec;
    }

    proof {
        assert forall |j: int| 0 <= j && j < s.len() ensures (s@[j] == '0' || s@[j] == '1') by {
            if j < start_index {
                assert(s@[j] == '0' || s@[j] == '1');
            } else {
                assert(s@[j] == '0' || s@[j] == '1');
            }
        }

        assert forall |k: int| start_index <= k && k < s.len() implies (s@[k] == '0' || s@[k] == '1') by {}
    }

    // Copy the remaining characters
    let sub_seq = s@.subrange(start_index, s.len() as int);
    for ch in sub_seq {
        res_vec.push(ch);
    }

    res_vec
}
// </vc-code>

fn main() {}
}
