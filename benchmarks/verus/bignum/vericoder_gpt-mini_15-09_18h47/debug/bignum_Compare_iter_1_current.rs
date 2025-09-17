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
proof fn str2int_prefix_step(s: Seq<char>, k: int)
    requires 0 <= k && k < s.len() as int,
    ensures Str2Int(s.subrange(0, k+1)) == 2 * Str2Int(s.subrange(0, k)) + (if s.index(k) == '1' { 1nat } else { 0nat }),
{
}

proof fn str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0,
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
    let seq1 = s1@;
    let seq2 = s2@;
    let n1 = seq1.len() as int;
    let n2 = seq2.len() as int;

    let mut i: int = 0;
    let mut acc1: nat = 0;
    while i < n1
        invariant
            0 <= i && i <= n1,
            acc1 == Str2Int(seq1.subrange(0, i)),
        decreases n1 - i
    {
        let bit = if seq1.index(i) == '1' { 1nat } else { 0nat };
        acc1 = 2 * acc1 + bit;
        i += 1;
    }

    let mut j: int = 0;
    let mut acc2: nat = 0;
    while j < n2
        invariant
            0 <= j && j <= n2,
            acc2 == Str2Int(seq2.subrange(0, j)),
        decreases n2 - j
    {
        let bit = if seq2.index(j) == '1' { 1nat } else { 0nat };
        acc2 = 2 * acc2 + bit;
        j += 1;
    }

    if acc1 < acc2 {
        return -1;
    } else if acc1 == acc2 {
        return 0;
    } else {
        return 1;
    }
}

// </vc-code>

fn main() {}
}


