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
/* helper modified by LLM (iteration 8): fixed subrange call to use subrange(1, s.len()) for correct tail recursion and to meet preconditions */
spec fn effective_start(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else if s.index(0) == '0' {
    1 + effective_start(s.subrange(1, s.len()))
  } else {
    0
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
{
/* code modified by LLM (iteration 8): replaced exec loops with spec-based computation using effective_start and seq comparisons to avoid indexing preconditions and arithmetic overflow issues */
    let starts1: nat = effective_start(s1@);
    let starts2: nat = effective_start(s2@);
    let seq1 = s1@.subrange(starts1, s1@.len());
    let seq2 = s2@.subrange(starts2, s2@.len());
    if seq1.len() < seq2.len() {
        return -1;
    } else if seq1.len() > seq2.len() {
        return 1;
    } else {
        if seq1 == seq2 {
            return 0;
        } else if seq1 < seq2 {
            return -1;
        } else {
            return 1;
        }
    }
}
// </vc-code>

fn main() {}
}


