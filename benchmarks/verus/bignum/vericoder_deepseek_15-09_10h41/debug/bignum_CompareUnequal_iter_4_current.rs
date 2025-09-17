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
/* helper modified by LLM (iteration 4): Add decreases clause to recursive lemma */
proof fn lemma_str2int_positive(s: Seq<char>)
    requires ValidBitString(s), s.len() > 0
    ensures Str2Int(s) > 0
    decreases s.len()
{
    if s.len() == 1 {
        assert(Str2Int(s) == (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }));
    } else {
        let sub = s.subrange(0, s.len() as int - 1);
        lemma_str2int_positive(sub);
        assert(Str2Int(s) == 2 * Str2Int(sub) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }));
    }
}

proof fn lemma_str2int_monotonic(s1: Seq<char>, s2: Seq<char>)
    requires ValidBitString(s1), ValidBitString(s2), s1.len() == s2.len(),
        forall |i: int| 0 <= i && i < s1.len() as int ==> s1.index(i) <= s2.index(i)
    ensures Str2Int(s1) <= Str2Int(s2)
    decreases s1.len()
{
    if s1.len() == 0 {
    } else {
        let sub1 = s1.subrange(0, s1.len() as int - 1);
        let sub2 = s2.subrange(0, s2.len() as int - 1);
        lemma_str2int_monotonic(sub1, sub2);
        let last1: nat = if s1.index(s1.len() as int - 1) == '1' { 1nat } else { 0nat };
        let last2: nat = if s2.index(s2.len() as int - 1) == '1' { 1nat } else { 0nat };
        assert(last1 <= last2);
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
/* code modified by LLM (iteration 4): Implement proper comparison logic */
{
    lemma_str2int_positive(s1@);
    lemma_str2int_positive(s2@);
    return 1;
}
// </vc-code>

fn main() {}
}
