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
/* helper modified by LLM (iteration 2): Changed return type of compare_str_as_ints to i32 */
spec fn compare_str_as_ints(s1: Seq<char>, s2: Seq<char>) -> i32
    requires
        ValidBitString(s1),
        ValidBitString(s2),
    ensures
        (Str2Int(s1) < Str2Int(s2)) ==> (compare_str_as_ints(s1, s2) == -1),
        (Str2Int(s1) == Str2Int(s2)) ==> (compare_str_as_ints(s1, s2) == 0),
        (Str2Int(s1) > Str2Int(s2)) ==> (compare_str_as_ints(s1, s2) == 1),

{
    if Str2Int(s1) < Str2Int(s2) {
        -1
    } else if Str2Int(s1) == Str2Int(s2) {
        0
    } else {
        1
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
/* code modified by LLM (iteration 2): Calls compare_str_as_ints helper */
{
        compare_str_as_ints(s1@, s2@)
}
// </vc-code>

fn main() {}
}


