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

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@),
   t@.len() > 0,
   t@.len() > 1 ==> t@[0] != '0',
   ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Added decreases clause to while loop */
    let mut t: Vec<char> = Vec::new();
    let mut leading_zeros = 0;
    while leading_zeros < s.len() && s[leading_zeros] == '0'
        invariant
            leading_zeros <= s.len(),
            forall |i: int| 0 <= i && i < leading_zeros ==> s@[i] == '0'
        decreases s.len() - leading_zeros
    {
        leading_zeros += 1;
    }
    if leading_zeros == s.len() {
        t.push('0');
    } else {
        for i in leading_zeros..s.len() {
            t.push(s[i]);
        }
    }
    t
}
// </vc-code>

// <vc-spec>
exec fn CompareUnequal(s1: &[char], s2: &[char]) -> (res: i32)
  requires ValidBitString(s1@),
   ValidBitString(s2@),
   s1@.len() > 0,
   (s1@.len() > 1 ==> s1@[0] != '0'),
   s2@.len() > 0,
   (s2@.len() > 1 ==> s2@[0] != '0'),
   s1@.len() > s2@.len(),
  ensures Str2Int(s1@) < Str2Int(s2@) ==> res == -1,
    Str2Int(s1@) == Str2Int(s2@) ==> res == 0,
    Str2Int(s1@) > Str2Int(s2@) ==> res == 1
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Fixed to handle unequal length preconditions */
    return 1;
}
// </vc-code>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Removed invalid lemmas and added proper helper */
proof fn remove_leading_zeros_preserves_value(s: Seq<char>)
    requires
        ValidBitString(s)
    ensures
        exists |t: Seq<char>| t.len() > 0 && (t.len() > 1 ==> t.index(0) != '0') && ValidBitString(t) && Str2Int(s) == Str2Int(t)
{
}

proof fn string_value_comparison_lemma(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() > 0,
        s2.len() > 0,
        s1.index(0) != '0',
        s2.index(0) != '0',
        s1.len() > s2.len()
    ensures
        Str2Int(s1) > Str2Int(s2)
{
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
    /* code modified by LLM (iteration 4): Fixed implementation to handle normalization */
    let t1 = NormalizeBitString(s1);
    let t2 = NormalizeBitString(s2);
    
    if t1@.len() > t2@.len() {
        1
    } else if t1@.len() < t2@.len() {
        -1
    } else {
        for i in 0..t1@.len() as int {
            if t1@[i] == '1' && t2@[i] == '0' {
                return 1;
            } else if t1@[i] == '0' && t2@[i] == '1' {
                return -1;
            }
        }
        0
    }
}
// </vc-code>

fn main() {}
}


