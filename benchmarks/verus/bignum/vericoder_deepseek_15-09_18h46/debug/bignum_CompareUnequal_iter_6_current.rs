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
/* helper modified by LLM (iteration 6): Fixed pow2 argument types to use nat */
use vstd::arithmetic::power2::pow2;

proof fn lemma_str2int_len_property(s: Seq<char>)  
  requires ValidBitString(s), s.len() > 0, (s.len() > 1 ==> s[0] != '0') 
  ensures Str2Int(s) >= pow2((s.len() as nat) - 1)
{
  if s.len() == 1 {
    assert(Str2Int(s) == 1nat);
    assert(pow2(0) == 1nat);
  } else {
    let sub = s.subrange(1, s.len() as int);
    lemma_str2int_len_property(sub);
    let val = Str2Int(s);
    assert(val == 2 * Str2Int(sub) + (if s[0] == '1' { 1nat } else { 0nat }));
    assert(Str2Int(sub) >= pow2((sub.len() as nat) - 1));
    assert(val >= 2 * pow2((sub.len() as nat) - 1));
    assert(val >= pow2((s.len() as nat) - 1));
  }
}

proof fn lemma_pow2_strictly_increasing(a: nat, b: nat)
  requires a < b
  ensures pow2(a) < pow2(b)
{
  if a + 1 == b {
    assert(pow2(b) == 2 * pow2(a));
  } else {
    let b_minus_1: nat = (b - 1) as nat;
    lemma_pow2_strictly_increasing(a, b_minus_1);
    lemma_pow2_strictly_increasing(b_minus_1, b);
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
/* code modified by LLM (iteration 6): Fixed pow2 argument types and improved verification */
{
    proof {
        let len1: nat = s1@.len() as nat;
        let len2: nat = s2@.len() as nat;
        
        lemma_str2int_len_property(s1@);
        lemma_str2int_len_property(s2@);
        assert(Str2Int(s1@) >= pow2(len1 - 1));
        assert(Str2Int(s2@) < pow2(len2));
        lemma_pow2_strictly_increasing(len2, len1);
        assert(Str2Int(s1@) > Str2Int(s2@));
    }
    return 1;
}
// </vc-code>

fn main() {}
}
