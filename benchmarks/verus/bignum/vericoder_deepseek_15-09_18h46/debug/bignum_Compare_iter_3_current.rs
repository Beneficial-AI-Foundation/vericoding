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
  // All characters must be '0' or '1'.
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
/* helper modified by LLM (iteration 3): Fixed compare_loop_helper and added utility helpers */
fn compare_loop_helper(a: int, b: int) -> int {
    if a < b { a } else { b }
}

proof fn compare_lemma(s1: Seq<char>, s2: Seq<char>)
    requires ValidBitString(s1), ValidBitString(s2),
    ensures Str2Int(s1) < Str2Int(s2) ==> Str2Int(s1) + 1 <= Str2Int(s2),
        Str2Int(s1) > Str2Int(s2) ==> Str2Int(s2) + 1 <= Str2Int(s1)
{
    if s1.len() > 0 && s2.len() > 0 {
        let s1_prefix = s1.subrange(0, s1.len() - 1);
        let s2_prefix = s2.subrange(0, s2.len() - 1);
        compare_lemma(s1_prefix, s2_prefix);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Compare(s1: &[char], s2: &[char]) -> (res: i32)
  requires ValidBitString(s1@),
   ValidBitString(s2@),
  ensures Str2Int(s1@) < Str2Int(s2@) ==> res == -1,
    Str2Int(s1@) == Str2Int(s2@) ==> res == 0,
    Str2Int(s1@) > Str2Int(s2@) ==> res == 1,
  decreases Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed result usage and added proper variable handling */
{
    let result: i32;
    
    if Str2Int(s1@) < Str2Int(s2@) {
        result = -1;
    } else if Str2Int(s1@) == Str2Int(s2@) {
        result = 0;
    } else {
        result = 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}


