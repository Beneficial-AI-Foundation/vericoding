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
    /* code modified by LLM (iteration 3): replaced spec type casts with proper usize indexing to fix compilation */
    let mut start: usize = 0;
    while start < s.len()
        invariant
            0 <= start <= s.len(),
            forall |i: int| 0 <= i < start ==> s@[i] == '0'
        decreases s.len() - start
    {
        if s@[start] != '0' {
            break;
        }
        start += 1;
    }
    let mut result: Vec<char> = Vec::new();
    if start == s.len() {
        result.push('0');
    } else {
        let mut j = start;
        while j < s.len()
            invariant
                start <= j <= s.len()
            decreases s.len() - j
        {
            result.push(s@[j]);
            j += 1;
        }
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
    /* code modified by LLM (iteration 3): no changes needed as it returns constant */
    1
}
// </vc-code>

// <vc-helpers>
/* helper modified by LLM (iteration 3): replaced spec type casts with proper usize indexing to fix compilation */
exec fn normalize(s: &[char]) -> (t: Vec<char>)
    requires true
    ensures
        ValidBitString(t@),
        t@.len() > 0,
        t@.len() > 1 ==> t@[0] != '0',
        ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
    decreases Str2Int(s@)
{
    let mut start: usize = 0;
    while start < s.len()
        invariant
            0 <= start <= s.len(),
            forall |i: int| 0 <= i < start ==> s@[i] == '0'
        decreases s.len() - start
    {
        if s@[start] != '0' {
            break;
        }
        start += 1;
    }
    let mut result: Vec<char> = Vec::new();
    if start == s.len() {
        result.push('0');
    } else {
        let mut j = start;
        while j < s.len()
            invariant
                start <= j <= s.len()
            decreases s.len() - j
        {
            result.push(s@[j]);
            j += 1;
        }
    }
    result
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
    /* code modified by LLM (iteration 3): replaced spec type casts with proper usize indexing to fix compilation */
    let s1_norm = normalize(&s1);
    let s2_norm = normalize(&s2);
    if s1_norm.len() > s2_norm.len() {
        1
    } else if s2_norm.len() > s1_norm.len() {
        -1
    } else {
        let mut i: usize = 0;
        while i < s1_norm.len()
            invariant
                0 <= i <= s1_norm.len()
            decreases s1_norm.len() - i
        {
            let c1 = s1_norm@[i];
            let c2 = s2_norm@[i];
            if c1 > c2 {
                return 1;
            } else if c1 < c2 {
                return -1;
            }
            i += 1;
        }
        0
    }
}
// </vc-code>

fn main() {}
}


