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

fn compare_loop_helper(a: usize, b: usize) -> usize
    ensures a as int == result as int
{
    a
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
    /* code modified by LLM (iteration 2): Fixed casting issues and added proper ghost code handling */
    let mut i = 0;
    let mut j = 0;
    
    while i < s1.len() && j < s2.len()
        invariant
            0 <= i <= s1.len(),
            0 <= j <= s2.len(),
            Str2Int(s1@.subrange(0, i)) <= Str2Int(s2@.subrange(0, j)) + 1,
            Str2Int(s2@.subrange(0, j)) <= Str2Int(s1@.subrange(0, i)) + 1
        decreases (s1.len() - i) + (s2.len() - j)
    {
        proof {
            let s1_rest = s1@.subrange(i, s1.len());
            let s2_rest = s2@.subrange(j, s2.len());
            
            if s1_rest.len() == 0 || s2_rest.len() == 0 {
                break;
            }
        }
        
        if s1[i] == s2[j] {
            i += 1;
            j += 1;
        } else if s1[i] == '1' {
            return 1;
        } else {
            return -1;
        }
    }
    
    match (s1.len() - i).cmp(&(s2.len() - j)) {
        std::cmp::Ordering::Less => -1,
        std::cmp::Ordering::Equal => 0,
        std::cmp::Ordering::Greater => 1,
    }
}
// </vc-code>

fn main() {}
}


