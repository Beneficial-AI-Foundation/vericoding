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
    let mut t: Vec<char> = Vec::new();
    let mut idx: usize = 0;
    while idx < s.len()
        invariant
            0 <= idx && idx <= s.len(),
        decreases s.len() as int - idx as int
    {
        t.push(s[idx]);
        idx += 1;
    }
    if t.len() == 0 {
        t.push('0');
    } else {
        while t.len() > 1 && t[0] == '0'
            invariant
                1 <= t.len(),
            decreases t.len() as int
        {
            t.remove(0);
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
    let mut v1: nat = 0;
    let mut v2: nat = 0;
    let n1: int = s1.len() as int;
    let n2: int = s2.len() as int;

    let mut i: int = 0;
    while i < n1
        invariant
            0 <= i && i <= n1,
            v1 == Str2Int(s1@.subrange(0, i)),
        decreases n1 - i
    {
        let bit: nat = if s1[i as usize] == '1' { 1 } else { 0 };
        v1 = 2 * v1 + bit;
        i += 1;
    }

    let mut j: int = 0;
    while j < n2
        invariant
            0 <= j && j <= n2,
            v2 == Str2Int(s2@.subrange(0, j)),
        decreases n2 - j
    {
        let bit: nat = if s2[j as usize] == '1' { 1 } else { 0 };
        v2 = 2 * v2 + bit;
        j += 1;
    }

    if v1 < v2 {
        -1
    } else if v1 == v2 {
        0
    } else {
        1
    }
}
// </vc-code>

// <vc-helpers>
proof fn Str2Int_subrange_last(s: Seq<char>, i: int)
    requires
        ValidBitString(s),
        0 <= i && i < s.len(),
    ensures
        Str2Int(s.subrange(0, i+1)) == 2 * Str2Int(s.subrange(0, i)) + (if s.index(i) == '1' { 1nat } else { 0nat }),
{
    // By the definition of Str2Int applied to the prefix s.subrange(0, i+1).
}

proof fn Str2Int_empty()
    ensures
        Str2Int(Seq::<char>::empty()) == 0nat,
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
    let mut v1: nat = 0;
    let mut v2: nat = 0;
    let n1: int = s1.len() as int;
    let n2: int = s2.len() as int;

    let mut i: int = 0;
    while i < n1
        invariant
            0 <= i && i <= n1,
            v1 == Str2Int(s1@.subrange(0, i)),
        decreases n1 - i
    {
        let bit: nat = if s1[i as usize] == '1' { 1 } else { 0 };
        v1 = 2 * v1 + bit;
        i += 1;
    }

    let mut j: int = 0;
    while j < n2
        invariant
            0 <= j && j <= n2,
            v2 == Str2Int(s2@.subrange(0, j)),
        decreases n2 - j
    {
        let bit: nat = if s2[j as usize] == '1' { 1 } else { 0 };
        v2 = 2 * v2 + bit;
        j += 1;
    }

    if v1 < v2 {
        -1
    } else if v1 == v2 {
        0
    } else {
        1
    }
}
// </vc-code>

fn main() {}
}


