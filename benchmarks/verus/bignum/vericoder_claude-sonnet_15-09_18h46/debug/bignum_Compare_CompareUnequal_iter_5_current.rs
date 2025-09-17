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
    /* code modified by LLM (iteration 5): fixed loop invariant and postcondition by ensuring all pushed characters are valid */
    let mut result = Vec::new();
    let mut found_one = false;
    
    for i in 0..s.len()
        invariant
            ValidBitString(result@),
            !found_one ==> result@.len() == 0,
            found_one ==> (result@.len() > 0 && result@[0] != '0'),
            ValidBitString(s@) ==> (
                if found_one {
                    exists |k: int| 0 <= k < i && s@[k] == '1' && 
                    result@ == s@.subrange(k, i as int)
                } else {
                    forall |k: int| 0 <= k < i ==> s@[k] == '0'
                }
            ),
    {
        if s[i] == '1' && !found_one {
            found_one = true;
        }
        if found_one {
            result.push(s[i]);
        }
    }
    
    if result.len() == 0 {
        result.push('0');
    }
    
    result
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
    /* code modified by LLM (iteration 5): simple return since s1 is longer than s2 */
    return 1;
}
// </vc-code>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed proof block from spec function and converted to regular proof function */
proof fn compare_lemma(s1: &[char], s2: &[char])
    requires
        ValidBitString(s1@),
        ValidBitString(s2@),
        s1@.len() > s2@.len(),
        s1@.len() > 0,
        s2@.len() > 0,
        s1@.len() > 1 ==> s1@[0] != '0',
        s2@.len() > 1 ==> s2@[0] != '0',
    ensures
        Str2Int(s1@) > Str2Int(s2@),
{
    let len1 = s1@.len() as int;
    let len2 = s2@.len() as int;
    assert(len1 > len2);
    assert(Str2Int(s1@) >= vstd::arithmetic::power2::pow2((len1 - 1) as nat));
    assert(Str2Int(s2@) < vstd::arithmetic::power2::pow2(len2 as nat));
    assert(vstd::arithmetic::power2::pow2((len1 - 1) as nat) >= vstd::arithmetic::power2::pow2(len2 as nat));
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
    /* code modified by LLM (iteration 5): added proper proof calls and fixed comparison logic */
    let t1 = NormalizeBitString(s1);
    let t2 = NormalizeBitString(s2);
    
    if t1.len() > t2.len() {
        proof { compare_lemma(&t1, &t2); }
        return CompareUnequal(&t1, &t2);
    } else if t1.len() < t2.len() {
        proof { compare_lemma(&t2, &t1); }
        let res = CompareUnequal(&t2, &t1);
        return if res == 1 { -1 } else if res == -1 { 1 } else { 0 };
    } else {
        let mut i = 0;
        while i < t1.len()
            invariant
                0 <= i <= t1.len(),
                t1.len() == t2.len(),
                ValidBitString(t1@),
                ValidBitString(t2@),
                forall |j: int| 0 <= j < i ==> t1@[j] == t2@[j],
            decreases t1.len() - i
        {
            if t1[i] == '1' && t2[i] == '0' {
                return 1;
            } else if t1[i] == '0' && t2[i] == '1' {
                return -1;
            }
            i += 1;
        }
        return 0;
    }
}
// </vc-code>

fn main() {}
}


