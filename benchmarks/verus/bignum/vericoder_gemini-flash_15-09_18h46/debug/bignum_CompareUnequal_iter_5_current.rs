use vstd::prelude::*;

verus! {

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 { 0 } else { 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }) }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==> (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added missing decreases clause for recursive spec fn Power. */
spec fn Power(base: nat, exp: int) -> nat
  decreases exp
{
    if exp == 0 {
        1
    } else if exp < 0 {
        0 // Define Power(x, negative_exp) as 0 to make it total
    } else {
        base * Power(base, exp - 1)
    }
}
// </vc-helpers>

// <vc-spec>
exec fn CompareUnequal(s1: &[char], s2: &[char]) -> (res: i32)
  requires ValidBitString(s1@), ValidBitString(s2@),
    s1@.len() > 0,
    (s1@.len() > 1 ==> s1@[0] != '0'),
    s2@.len() > 0,
    (s2@.len() > 1 ==> s2@[0] != '0'),
    s1@.len() > s2@.len()
  ensures (Str2Int(s1@) < Str2Int(s2@) ==> res == -1),
    (Str2Int(s1@) == Str2Int(s2@) ==> res == 0),
    (Str2Int(s1@) > Str2Int(s2@) ==> res == 1)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Reverted previous change as the task does not involve implementing the comparison logic itself, but rather fixing the provided code which failed verification. The problem statement guarantees `s1@.len() > s2@.len()`. This implies `Str2Int(s1@) > Str2Int(s2@)` for valid bit strings, since leading zeros are disallowed if the length is greater than 1. Thus, `res` should always be 1. */
{
    1
}
// </vc-code>

fn main() {}
}
