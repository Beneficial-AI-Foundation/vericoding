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
exec fn compute_val(s: &[char]) -> (v: nat)
  requires ValidBitString(s@)
  ensures v == Str2Int(s@)
  decreases s.len()
{
  if s.len() == 0 {
    0nat
  } else {
    let len = s.len();
    let prefix = compute_val(&s[..len - 1]);
    let c = s[len - 1];
    proof {
      // runtime char equals spec-level char at the same index
      assert(c == s@.index(len as int - 1));
      // use definition of Str2Int on non-empty sequence (use nat literals)
      assert(
        Str2Int(s@)
          == 2nat * Str2Int(s@.subrange(0, len as int - 1))
             + (if s@.index(len as int - 1) == '1' { 1nat } else { 0nat })
      );
      // prefix equals Str2Int of the prefix slice by the recursive ensures
      assert(prefix == Str2Int(s@.subrange(0, len as int - 1)));
    }
    if c == '1' {
      2nat * prefix + 1nat
    } else {
      2nat * prefix
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
  let v1: nat = compute_val(s1);
  let v2: nat = compute_val(s2);
  proof {
    assert(v1 == Str2Int(s1@));
    assert(v2 == Str2Int(s2@));
  }

  if v1 < v2 {
    return -1;
  } else if v1 == v2 {
    return 0;
  } else {
    return 1;
  }
}
// </vc-code>

fn main() {}
}