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
/* helper modified by LLM (iteration 2): Fix indexing syntax from s@[i] to s[i] and add type annotations */
proof fn lemma_str2int_positive(s: Seq<char>) 
    requires ValidBitString(s), s.len() > 0
    ensures Str2Int(s) > 0
{
    if s.len() == 1 {
        assert(Str2Int(s) == (if s[s.len() as int - 1] == '1' { 1 } else { 0 }));
    } else {
        let sub = s.subrange(0, s.len() as int - 1);
        lemma_str2int_positive(sub);
        assert(Str2Int(s) == 2 * Str2Int(sub) + (if s[s.len() as int - 1] == '1' { 1 } else { 0 }));
    }
}

proof fn lemma_str2int_monotonic(s1: Seq<char>, s2: Seq<char>)
    requires ValidBitString(s1), ValidBitString(s2), s1.len() == s2.len(),
        forall |i: int| 0 <= i && i < s1.len() as int ==> s1[i] <= s2[i]
    ensures Str2Int(s1) <= Str2Int(s2)
{
    if s1.len() == 0 {
    } else {
        let sub1 = s1.subrange(0, s1.len() as int - 1);
        let sub2 = s2.subrange(0, s2.len() as int - 1);
        lemma_str2int_monotonic(sub1, sub2);
        let last1 = if s1[s1.len() as int - 1] == '1' { 1 } else { 0 };
        let last2 = if s2[s2.len() as int - 1] == '1' { 1 } else { 0 };
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
/* code modified by LLM (iteration 2): Fix indexing syntax from s@[i] to s[i] and ensure proper comparison logic */
{
    let len1: usize = s1.len();
    let len2: usize = s2.len();
    
    proof {
        lemma_str2int_positive(s1@);
        lemma_str2int_positive(s2@);
    }
    
    if len1 > len2 {
        return 1;
    } else if len1 < len2 {
        return -1;
    }
    
    let mut i: usize = 0;
    while i < len1
        invariant
            0 <= i && i <= len1,
            forall |j: int| 0 <= j && j < i as int ==> s1@[j] == s2@[j],
            Str2Int(s1@.subrange(0, i as int)) == Str2Int(s2@.subrange(0, i as int))
    {
        if s1[i] < s2[i] {
            return -1;
        } else if s1[i] > s2[i] {
            return 1;
        }
        i += 1;
    }
    
    return 0;
}
// </vc-code>

fn main() {}
}
