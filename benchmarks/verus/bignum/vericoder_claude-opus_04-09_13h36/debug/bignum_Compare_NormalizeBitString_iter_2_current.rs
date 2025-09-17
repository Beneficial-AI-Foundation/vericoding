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
proof fn str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{
    assert(Seq::<char>::empty().len() == 0);
}

proof fn str2int_single_zero()
    ensures Str2Int(seq!['0']) == 0
{
    assert(seq!['0'].len() == 1);
    assert(seq!['0'].subrange(0, 0) == Seq::<char>::empty());
    assert(Str2Int(seq!['0'].subrange(0, 0)) == 0);
    assert(seq!['0'].index(0) == '0');
}

proof fn str2int_single_one()
    ensures Str2Int(seq!['1']) == 1
{
    assert(seq!['1'].len() == 1);
    assert(seq!['1'].subrange(0, 0) == Seq::<char>::empty());
    assert(Str2Int(seq!['1'].subrange(0, 0)) == 0);
    assert(seq!['1'].index(0) == '1');
}

proof fn str2int_leading_zeros(s: Seq<char>)
    requires ValidBitString(s),
             s.len() > 0,
             s.index(0) == '0'
    ensures Str2Int(s) == Str2Int(s.subrange(1, s.len() as int))
    decreases s.len()
{
    if s.len() == 1 {
        assert(s.subrange(1, s.len() as int) == Seq::<char>::empty());
        str2int_single_zero();
        str2int_empty();
    } else {
        assert(s.subrange(0, s.len() as int - 1).index(0) == '0');
        if s.len() > 2 {
            str2int_leading_zeros(s.subrange(0, s.len() as int - 1));
        }
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
{
    let n1 = s1.len();
    let n2 = s2.len();
    
    // Find first non-zero position in s1
    let mut i1: usize = 0;
    while i1 < n1
        invariant 0 <= i1 <= n1,
                  forall |k: int| 0 <= k && k < i1 ==> s1@.index(k) == '0',
                  i1 > 0 ==> Str2Int(s1@) == Str2Int(s1@.subrange(i1 as int, n1 as int))
    {
        if s1[i1] != '0' {
            break;
        }
        proof {
            if i1 > 0 {
                str2int_leading_zeros(s1@.subrange(i1 as int - 1, n1 as int));
            }
        }
        i1 = i1 + 1;
    }
    
    // Find first non-zero position in s2
    let mut i2: usize = 0;
    while i2 < n2
        invariant 0 <= i2 <= n2,
                  forall |k: int| 0 <= k && k < i2 ==> s2@.index(k) == '0',
                  i2 > 0 ==> Str2Int(s2@) == Str2Int(s2@.subrange(i2 as int, n2 as int))
    {
        if s2[i2] != '0' {
            break;
        }
        proof {
            if i2 > 0 {
                str2int_leading_zeros(s2@.subrange(i2 as int - 1, n2 as int));
            }
        }
        i2 = i2 + 1;
    }
    
    let len1 = n1 - i1;
    let len2 = n2 - i2;
    
    // Compare lengths first (longer number is greater)
    if len1 < len2 {
        return -1;
    } else if len1 > len2 {
        return 1;
    }
    
    // Same length, compare digit by digit
    let mut j: usize = 0;
    while j < len1
        invariant 0 <= j <= len1,
                  len1 == len2,
                  i1 + j <= n1,
                  i2 + j <= n2,
                  forall |k: int| 0 <= k && k < j ==> s1@.index(i1 as int + k) == s2@.index(i2 as int + k)
    {
        if s1[i1 + j] < s2[i2 + j] {
            return -1;
        } else if s1[i1 + j] > s2[i2 + j] {
            return 1;
        }
        j = j + 1;
    }
    
    return 0;
}
// </vc-code>

fn main() {}
}