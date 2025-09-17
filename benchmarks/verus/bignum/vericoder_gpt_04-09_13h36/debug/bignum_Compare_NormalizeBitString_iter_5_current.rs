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
proof fn valid_bitstring_prefix(s: Seq<char>, k: int)
  requires
    0 <= k <= s.len() as int,
    ValidBitString(s),
  ensures
    ValidBitString(s.subrange(0, k))
{
  assert forall |i: int|
    0 <= i && i < k ==>
      s.subrange(0, k).index(i) == '0' || s.subrange(0, k).index(i) == '1'
  by {
    if 0 <= i && i < k {
      assert(0 <= i && i < s.len() as int);
      assert(s.subrange(0, k).index(i) == s.index(i));
      assert(s.index(i) == '0' || s.index(i) == '1');
    }
  }
}

proof fn str2int_unfold_nonempty(t: Seq<char>)
  requires
    t.len() > 0,
    ValidBitString(t),
  ensures
    Str2Int(t)
      == 2 * Str2Int(t.subrange(0, t.len() as int - 1))
         + (if t.index(t.len() as int - 1) == '1' { 1nat } else { 0nat })
{
  reveal(Str2Int);
}

exec fn ExecStr2Int(s: &[char]) -> (v: nat)
  requires
    ValidBitString(s@),
  ensures
    v == Str2Int(s@)
{
  let mut i: usize = 0;
  let mut acc: nat = 0;

  proof {
    valid_bitstring_prefix(s@, 0);
    reveal(Str2Int);
    assert(Str2Int(s@.subrange(0, 0)) == 0);
  }

  while i < s.len()
    invariant
      0 <= i as int && i as int <= s.len() as int,
      ValidBitString(s@),
      ValidBitString(s@.subrange(0, i as int)),
      acc == Str2Int(s@.subrange(0, i as int))
    decreases s.len() as int - i as int
  {
    let bit_is_one = s[i] == '1';
    let bitval: nat = if bit_is_one { 1nat } else { 0nat };
    let old_acc = acc;
    acc = old_acc + old_acc + bitval;

    proof {
      let k = i as int;
      assert(k < s.len() as int);
      assert(s@.index(k) == s[i]);
      assert(bitval == (if s@.index(k) == '1' { 1nat } else { 0nat }));

      let u = s@.subrange(0, k + 1);
      valid_bitstring_prefix(s@, k + 1);
      assert(u.len() as int == k + 1);
      assert(u.index(u.len() as int - 1) == s@.index(k));
      assert(u.subrange(0, u.len() as int - 1) == s@.subrange(0, k));

      str2int_unfold_nonempty(u);

      assert(old_acc == Str2Int(s@.subrange(0, k)));
      assert(acc == 2 * old_acc + (if s@.index(k) == '1' { 1nat } else { 0nat }));
      assert(acc == 2 * Str2Int(s@.subrange(0, k)) + (if s@.index(k) == '1' { 1nat } else { 0nat }));
      assert(acc == Str2Int(u));
      assert(u == s@.subrange(0, k + 1));
    }

    i = i + 1;

    proof {
      valid_bitstring_prefix(s@, i as int);
      assert(acc == Str2Int(s@.subrange(0, i as int)));
    }
  }

  acc
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
  let n1 = ExecStr2Int(s1);
  let n2 = ExecStr2Int(s2);
  if n1 < n2 {
    -1
  } else if n1 == n2 {
    0
  } else {
    1
  }
}
// </vc-code>

fn main() {}
}