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
/* code modified by LLM (iteration 5): The previous implementation was attempting to use `s1@` and `s2@` directly, which returns a `vstd::view::View<[char]>` (spec mode only). Replaced it with `s1.len()` and `s2.len()` for the length comparisons, and `Str2Int(s1.view())` and `Str2Int(s2.view())` for the `Str2Int` comparisons. `view()` is callable in exec mode and returns the spec-mode sequence view. */
{
    if s1.len() < s2.len() {
        -1
    } else if s1.len() > s2.len() {
        1
    } else {
        if Str2Int(s1.view()) < Str2Int(s2.view()) {
            -1
        } else if Str2Int(s1.view()) == Str2Int(s2.view()) {
            0
        } else {
            1
        }
    }
}
// </vc-code>

fn main() {}
}


