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
proof fn Str2Int_monotonic(s1: Seq<char>, s2: Seq<char>)
    requires s1.len() < s2.len(),
        ValidBitString(s1),
        ValidBitString(s2),
        forall |i: int| 0 <= i && i < s1.len() as int ==> s1.index(i) == s2.index(i)
    ensures Str2Int(s1) < Str2Int(s2)
{
    if s1.len() > 0 {
        let s1' = s1.subrange(0, s1.len() as int - 1);
        let s2' = s2.subrange(0, s1.len() as int - 1);
        Str2Int_monotonic(s1', s2');
        assert(Str2Int(s1) == 2 * Str2Int(s1') + 
            (if s1.index(s1.len() as int - 1) == '1' { 1nat } else { 0nat }));
        assert(Str2Int(s2) > 2 * Str2Int(s2') + 
            (if s2.index(s1.len() as int - 1) == '1' { 1nat } else { 0nat }));
    }
}

spec fn EqualOrPrecedes(s1: Seq<char>, s2: Seq<char>) -> bool
{
    s1.len() < s2.len() ||
    (s1.len() == s2.len() &&
        (forall |i: int| 0 <= i && i < s1.len() as int ==> s1.index(i) == s2.index(i)))
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
    let n1 = s1.len();
    let n2 = s2.len();
    
    // Compare lengths first
    if n1 < n2 {
        return -1;
    } else if n1 > n2 {
        return 1;
    }
    
    // Equal length, compare bit by bit
    let mut i: usize = 0;
    while i < n1
        invariant
            0 <= i && i <= n1,
            forall |j: int| 0 <= j && j < i as int ==> s1@[j] == s2@[j]
        decreases n1 - i
    {
        if s1[i] != s2[i] {
            return if s1[i] == '1' { 1 } else { -1 };
        }
        i += 1;
    }
    
    return 0;
}
// </vc-code>

fn main() {}
}


