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
spec fn Power(base: nat, exp: nat) -> nat {
    if exp == 0 {
        1
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
{
    let len1 = s1.len();
    let len2 = s2.len();

    if len1 > len2 {
        1
    } else if len2 > len1 {
        -1
    } else {
        let mut i = 0;
        while i < len1
            invariant
                0 <= i && i <= len1,
        {
            if s1[i] == '0' && s2[i] == '1' {
                return -1;
            } else if s1[i] == '1' && s2[i] == '0' {
                return 1;
            }
            i = i + 1;
        }
        0
    }
}
// </vc-code>

fn main() {}
}
