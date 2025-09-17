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
proof fn lemma_longer_string_greater_value(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() > 0,
        s2.len() > 0,
        s1.len() > s2.len(),
        s1.len() > 1 ==> s1[0] != '0',
        s2.len() > 1 ==> s2[0] != '0'
    ensures Str2Int(s1) >= Str2Int(s2)
{
    if s1.len() == 1 {
        if s2.len() == 1 {
            // Both single chars, s1 is at least as large
        }
    } else {
        // s1 has multiple chars and starts with '1'
        // s1 represents at least 2^(s1.len()-1)
        // s2 represents at most 2^(s2.len()) - 1
        // Since s1.len() > s2.len(), we have 2^(s1.len()-1) >= 2^(s2.len()-1) >= s2
        lemma_power_comparison(s1.len() as nat, s2.len() as nat);
    }
}

proof fn lemma_power_comparison(len1: nat, len2: nat)
    requires len1 > len2, len2 > 0
    ensures nat_pow(2, len1 - 1) >= nat_pow(2, len2) - 1
{
}

spec fn nat_pow(base: nat, exp: nat) -> nat
    decreases exp
{
    if exp == 0 { 1 } else { base * nat_pow(base, exp - 1) }
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
    proof {
        lemma_longer_string_greater_value(s1@, s2@);
    }
    return 1;
}
// </vc-code>

fn main() {}
}
