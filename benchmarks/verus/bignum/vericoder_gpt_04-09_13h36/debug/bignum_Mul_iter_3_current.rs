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
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
proof fn lemma_valid_subrange(s: Seq<char>, i: int, j: int)
  requires
    ValidBitString(s),
    0 <= i,
    i <= j,
    j <= s.len() as int
  ensures
    ValidBitString(s.subrange(i, j))
{
  assert(forall |k: int|
    0 <= k && k < s.subrange(i, j).len() as int ==>
      s.subrange(i, j).index(k) == '0' || s.subrange(i, j).index(k) == '1'
  ) by {
    assert(s.subrange(i, j).len() as int == j - i);
    assert(forall |k: int|
      0 <= k && k < j - i ==>
        s.subrange(i, j).index(k) == s.index(i + k)
    ) by { }
    assert(forall |k: int|
      0 <= k && k < j - i ==>
        s.index(i + k) == '0' || s.index(i + k) == '1'
    ) by {
      assert(0 <= i + k && i + k < s.len() as int);
      assert(ValidBitString(s));
    }
  }
}

proof fn lemma_valid_push(s: Seq<char>, b: char)
  requires
    ValidBitString(s),
    b == '0' || b == '1'
  ensures
    ValidBitString(s.push(b))
{
  assert(forall |k: int|
    0 <= k && k < s.push(b).len() as int ==>
      s.push(b).index(k) == '0' || s.push(b).index(k) == '1'
  ) by {
    if k < s.len() as int {
      assert(s.push(b).index(k) == s.index(k));
      assert(ValidBitString(s));
    } else {
      assert(k == s.len() as int);
      assert(s.push(b).index(k) == b);
    }
  }
}

proof fn lemma_subrange_push_equiv(s: Seq<char>, i: int)
  requires
    0 <= i,
    i < s.len() as int
  ensures
    s.subrange(0, i + 1) == s.subrange(0, i).push(s.index(i))
{
  let left = s.subrange(0, i + 1);
  let right = s.subrange(0, i).push(s.index(i));
  assert(left.len() as int == i + 1);
  assert(right.len() as int == i + 1);
  assert(forall |k: int|
    0 <= k && k < i + 1 ==> left.index(k) == right.index(k)
  ) by {
    if k < i {
      assert(left.index(k) == s.index(k));
      assert(right.index(k) == s.subrange(0, i).index(k));
      assert(right.index(k) == s.index(k));
    } else {
      assert(k == i);
      assert(left.index(k) == s.index(i));
      assert(right.index(k) == s.index(i));
    }
  }
}

proof fn lemma_Str2Int_push(s: Seq<char>, b: char)
  requires
    ValidBitString(s),
    b == '0' || b == '1'
  ensures
    Str2Int(s.push(b)) == 2 * Str2Int(s) + (if b == '1' { 1 } else { 0 })
  decreases s.len()
{
  let t = s.push(b);
  lemma_valid_push(s, b);
  assert(ValidBitString(t));
  assert(t.len() > 0);
  assert(t.subrange(0, t.len() as int - 1) == s) by {
    // t = s.push(b), so removing last element yields s
    let tl = t.len() as int;
    assert(tl == s.len() as int + 1);
    assert(t.subrange(0, tl - 1) == s);
  }
  assert(t.index(t.len() as int - 1) == b);
  assert(
    Str2Int(t)
    ==
    2 * Str2Int(t.subrange(0, t.len() as int - 1))
      + (if t.index(t.len() as int - 1) == '1' { 1nat } else { 0nat })
  );
  assert(Str2Int(t.subrange(0, t.len() as int - 1)) == Str2Int(s));
  assert((if t.index(t.len() as int - 1) == '1' { 1nat } else { 0nat })
          == (if b == '1' { 1nat } else { 0nat }));
}

exec fn ExecStr2Int(s: &[char]) -> (n: nat)
  requires
    ValidBitString(s@)
  ensures
    n == Str2Int(s@)
{
  let mut i: usize = 0;
  let mut acc: nat = 0;
  while i < s.len()
    invariant
      0 <= i as int && i as int <= s.len() as int,
      ValidBitString(s@),
      acc == Str2Int(s@.subrange(0, i as int))
    decreases s.len() as int - i as int
  {
    let c = s[i];
    proof {
      assert(0 <= i as int && i as int < s.len() as int);
      lemma_valid_subrange(s@, 0, i as int);
      assert(ValidBitString(s@.subrange(0, i as int)));
      assert(ValidBitString(s@));
      assert(s@.index(i as int) == c);
      assert(c == '0' || c == '1') by {
        assert(ValidBitString(s@));
        assert(0 <= i as int && i as int < s.len() as int);
      }
      lemma_Str2Int_push(s@.subrange(0, i as int), c);
      lemma_subrange_push_equiv(s@, i as int);
      assert(s@.subrange(0, i as int + 1) == s@.subrange(0, i as int).push(c));
    }
    acc = 2 * acc + (if c == '1' { 1 } else { 0 });
    i = i
// </vc-helpers>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
proof fn lemma_valid_subrange(s: Seq<char>, i: int, j: int)
  requires
    ValidBitString(s),
    0 <= i,
    i <= j,
    j <= s.len() as int
  ensures
    ValidBitString(s.subrange(i, j))
{
  assert(forall |k: int|
    0 <= k && k < s.subrange(i, j).len() as int ==>
      s.subrange(i, j).index(k) == '0' || s.subrange(i, j).index(k) == '1'
  ) by {
    assert(s.subrange(i, j).len() as int == j - i);
    assert(forall |k: int|
      0 <= k && k < j - i ==>
        s.subrange(i, j).index(k) == s.index(i + k)
    ) by { }
    assert(forall |k: int|
      0 <= k && k < j - i ==>
        s.index(i + k) == '0' || s.index(i + k) == '1'
    ) by {
      assert(0 <= i + k && i + k < s.len() as int);
      assert(ValidBitString(s));
    }
  }
}

proof fn lemma_valid_push(s: Seq<char>, b: char)
  requires
    ValidBitString(s),
    b == '0' || b == '1'
  ensures
    ValidBitString(s.push(b))
{
  assert(forall |k: int|
    0 <= k && k < s.push(b).len() as int ==>
      s.push(b).index(k) == '0' || s.push(b).index(k) == '1'
  ) by {
    if k < s.len() as int {
      assert(s.push(b).index(k) == s.index(k));
      assert(ValidBitString(s));
    } else {
      assert(k == s.len() as int);
      assert(s.push(b).index(k) == b);
    }
  }
}

proof fn lemma_subrange_push_equiv(s: Seq<char>, i: int)
  requires
    0 <= i,
    i < s.len() as int
  ensures
    s.subrange(0, i + 1) == s.subrange(0, i).push(s.index(i))
{
  let left = s.subrange(0, i + 1);
  let right = s.subrange(0, i).push(s.index(i));
  assert(left.len() as int == i + 1);
  assert(right.len() as int == i + 1);
  assert(forall |k: int|
    0 <= k && k < i + 1 ==> left.index(k) == right.index(k)
  ) by {
    if k < i {
      assert(left.index(k) == s.index(k));
      assert(right.index(k) == s.subrange(0, i).index(k));
      assert(right.index(k) == s.index(k));
    } else {
      assert(k == i);
      assert(left.index(k) == s.index(i));
      assert(right.index(k) == s.index(i));
    }
  }
}

proof fn lemma_Str2Int_push(s: Seq<char>, b: char)
  requires
    ValidBitString(s),
    b == '0' || b == '1'
  ensures
    Str2Int(s.push(b)) == 2 * Str2Int(s) + (if b == '1' { 1 } else { 0 })
  decreases s.len()
{
  let t = s.push(b);
  lemma_valid_push(s, b);
  assert(ValidBitString(t));
  assert(t.len() > 0);
  assert(t.subrange(0, t.len() as int - 1) == s) by {
    // t = s.push(b), so removing last element yields s
    let tl = t.len() as int;
    assert(tl == s.len() as int + 1);
    assert(t.subrange(0, tl - 1) == s);
  }
  assert(t.index(t.len() as int - 1) == b);
  assert(
    Str2Int(t)
    ==
    2 * Str2Int(t.subrange(0, t.len() as int - 1))
      + (if t.index(t.len() as int - 1) == '1' { 1nat } else { 0nat })
  );
  assert(Str2Int(t.subrange(0, t.len() as int - 1)) == Str2Int(s));
  assert((if t.index(t.len() as int - 1) == '1' { 1nat } else { 0nat })
          == (if b == '1' { 1nat } else { 0nat }));
}

exec fn ExecStr2Int(s: &[char]) -> (n: nat)
  requires
    ValidBitString(s@)
  ensures
    n == Str2Int(s@)
{
  let mut i: usize = 0;
  let mut acc: nat = 0;
  while i < s.len()
    invariant
      0 <= i as int && i as int <= s.len() as int,
      ValidBitString(s@),
      acc == Str2Int(s@.subrange(0, i as int))
    decreases s.len() as int - i as int
  {
    let c = s[i];
    proof {
      assert(0 <= i as int && i as int < s.len() as int);
      lemma_valid_subrange(s@, 0, i as int);
      assert(ValidBitString(s@.subrange(0, i as int)));
      assert(ValidBitString(s@));
      assert(s@.index(i as int) == c);
      assert(c == '0' || c == '1') by {
        assert(ValidBitString(s@));
        assert(0 <= i as int && i as int < s.len() as int);
      }
      lemma_Str2Int_push(s@.subrange(0, i as int), c);
      lemma_subrange_push_equiv(s@, i as int);
      assert(s@.subrange(0, i as int + 1) == s@.subrange(0, i as int).push(c));
    }
    acc = 2 * acc + (if c == '1' { 1 } else { 0 });
    i = i
// </vc-code>

fn main() {}
}