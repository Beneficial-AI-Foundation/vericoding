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
/* helper modified by LLM (iteration 3): relate Str2Int for prefix step */
proof fn str2int_prefix_step(s: Seq<char>, k: int)
    requires 0 <= k && k < s.len() as int,
    ensures Str2Int(s.subrange(0, k+1)) == 2 * Str2Int(s.subrange(0, k)) + (if s.index(k) == '1' { 1nat } else { 0nat }),
{
    // s.subrange(0, k+1) has length k+1
    assert(s.subrange(0, k+1).len() == (k + 1) as int);
    // By the definition of Str2Int on a non-empty sequence
    assert(Str2Int(s.subrange(0, k+1)) ==
           2 * Str2Int(s.subrange(0, k)) + (if s.subrange(0, k+1).index((k+1) as int - 1) == '1' { 1nat } else { 0nat }));
    // The last character of s.subrange(0, k+1) is s.index(k)
    assert(s.subrange(0, k+1).index((k+1) as int - 1) == s.index(k));
    assert((if s.subrange(0, k+1).index((k+1) as int - 1) == '1' { 1nat } else { 0nat }) == (if s.index(k) == '1' { 1nat } else { 0nat }));
}

/* helper modified by LLM (iteration 3): Str2Int of empty sequence is zero */
proof fn str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0,
{
    assert(Str2Int(Seq::<char>::empty()) == 0);
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
    /* code modified by LLM (iteration 3): compare by trimming leading zeros and lexicographic comparison with verification loop invariants */
    let n1: int = s1.len() as int;
    let n2: int = s2.len() as int;

    let mut p1: int = 0;
    while p1 < n1 && s1[p1 as usize] != '1'
        invariant
            0 <= p1 && p1 <= n1,
        decreases n1 - p1
    {
        p1 += 1;
    }

    let mut p2: int = 0;
    while p2 < n2 && s2[p2 as usize] != '1'
        invariant
            0 <= p2 && p2 <= n2,
        decreases n2 - p2
    {
        p2 += 1;
    }

    let eff1: int = if p1 == n1 { 0 } else { n1 - p1 };
    let eff2: int = if p2 == n2 { 0 } else { n2 - p2 };

    if eff1 < eff2 {
        return -1;
    } else if eff1 > eff2 {
        return 1;
    } else {
        if eff1 == 0 {
            return 0;
        }
        let mut k: int = 0;
        while k < eff1
            invariant
                0 <= k && k <= eff1,
            decreases eff1 - k
        {
            let b1 = s1[(p1 + k) as usize];
            let b2 = s2[(p2 + k) as usize];
            if b1 == b2 {
                k += 1;
                continue;
            } else if b1 == '0' && b2 == '1' {
                return -1;
            } else {
                return 1;
            }
        }
        return 0;
    }
}
// </vc-code>

fn main() {}
}


