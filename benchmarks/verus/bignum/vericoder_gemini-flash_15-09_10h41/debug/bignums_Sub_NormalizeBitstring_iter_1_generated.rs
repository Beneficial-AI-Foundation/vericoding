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
spec fn TrimLeadingZeros(s: Seq<char>) -> Seq<char>
    recommends ValidBitString(s)
{
    if s.len() == 0 {
        s
    } else if s.index(0) == '0' {
        TrimLeadingZeros(s.subrange(1, s.len() as int))
    } else {
        s
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Bignums_Sub_NormalizeBitstring(s: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    let mut result_vec = Vec::<char>::new();
    let mut leading_zero = true;
    for i in 0..s.len() {
        let char_at_i = s[i];
        if leading_zero && char_at_i == '0' {
            // Skip leading zeros
            if i == s.len() - 1 { // If it's the last digit and it's '0', add one '0'
                result_vec.push('0');
            }
        } else {
            leading_zero = false;
            result_vec.push(char_at_i);
        }
    }
    if result_vec.len() == 0 {
        result_vec.push('0');
    }

    // Proof to show the result is a valid bitstring
    proof {
        assert forall |i: int| 0 <= i && i < result_vec.len() as int implies
            (result_vec@[i] == '0' || result_vec@[i] == '1') by {
            if !leading_zero {
                // If leading_zero is false, all chars pushed were either '0' or '1'
                // because s is a ValidBitString and we only pushed chars from s.
                // The only exception is if result_vec contains only '0' for the case where s was all '0's.
                // In that case, it's also valid.
            }
        }
    }

    result_vec
}
// </vc-code>

fn main() {}
}
