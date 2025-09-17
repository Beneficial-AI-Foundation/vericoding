use vstd::prelude::*;

verus! {

spec fn AllZero(s: Seq<char>) -> bool
{
  s.len() == 0 || forall |i: int| 0 <= i && i < s.len() as int ==> s.index(i) == '0'
}

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 { 0 } else { 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }) }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==> (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
proof fn lemma_all_zero_implies_valid(s: Seq<char>)
  requires
    AllZero(s)
  ensures
    ValidBitString(s)
{
  if s.len() == 0 {
    assert(ValidBitString(s));
  } else {
    assert(forall |i: int| 0 <= i && i < s.len() as int ==> s.index(i) == '0') by {
      assert(s.len() != 0);
    }
    assert(forall |i: int|
      0 <= i && i < s.len() as int ==> #[trigger] s.index(i) == '0' || s.index(i) == '1'
    ) by {
      assert(forall |i: int| 0 <= i && i < s.len() as int ==> s.index(i) == '0');
    }
  }
}

proof fn lemma_all_zero_push(s: Seq<char>)
  requires
    AllZero(s)
  ensures
    AllZero(s.push('0'))
{
  if s.len() == 0 {
    assert(s.push('0').len() == 1);
    assert(forall |i: int|
      0 <= i && i < s.push('0').len() as int ==> #[trigger] s.push('0').index(i) == '0'
    ) by {
      assert(s.push('0').index(0) == '0');
    }
  } else {
    assert(s.len() != 0);
    assert(forall |i: int| 0 <= i && i < s.len() as int ==> s.index(i) == '0') by { }
    assert(forall |i: int|
      0 <= i && i < s.push('0').len() as int ==> #[trigger] s.push('0').index(i) == '0'
    ) by {
      assert(s.push('0').len() == s.len() + 1);
      assert(forall |i: int|
        0 <= i && i < s.len() as int ==> s.push('0').index(i) == s.index(i)
      ) by { }
      assert(s.push('0').index(s.len() as int) == '0');
    }
  }
}

proof fn lemma_all_zero_subrange_prefix(s: Seq<char>, m: int)
  requires
    AllZero(s),
    0 <= m && m <= s.len() as int
  ensures
    AllZero(s.subrange(0, m))
{
  if m == 0 {
    let t = s.subrange(0, 0);
    assert(t.len() == 0);
  } else {
    assert(m > 0);
    // Since m <= s.len(), s is non-empty
    assert(s.len() > 0);
    assert(forall |i: int| 0 <= i && i < s.len() as int ==> s
// </vc-helpers>

// <vc-spec>
exec fn Zeros(n: int) -> (s: Vec<char>)
  requires n >= 0
  ensures s@.len() == n as nat, ValidBitString(s@), Str2Int(s@) == 0, AllZero(s@)
// </vc-spec>
// <vc-code>
proof fn lemma_all_zero_implies_valid(s: Seq<char>)
  requires
    AllZero(s)
  ensures
    ValidBitString(s)
{
  if s.len() == 0 {
    assert(ValidBitString(s));
  } else {
    assert(forall |i: int| 0 <= i && i < s.len() as int ==> s.index(i) == '0') by {
      assert(s.len() != 0);
    }
    assert(forall |i: int|
      0 <= i && i < s.len() as int ==> #[trigger] s.index(i) == '0' || s.index(i) == '1'
    ) by {
      assert(forall |i: int| 0 <= i && i < s.len() as int ==> s.index(i) == '0');
    }
  }
}

proof fn lemma_all_zero_push(s: Seq<char>)
  requires
    AllZero(s)
  ensures
    AllZero(s.push('0'))
{
  if s.len() == 0 {
    assert(s.push('0').len() == 1);
    assert(forall |i: int|
      0 <= i && i < s.push('0').len() as int ==> #[trigger] s.push('0').index(i) == '0'
    ) by {
      assert(s.push('0').index(0) == '0');
    }
  } else {
    assert(s.len() != 0);
    assert(forall |i: int| 0 <= i && i < s.len() as int ==> s.index(i) == '0') by { }
    assert(forall |i: int|
      0 <= i && i < s.push('0').len() as int ==> #[trigger] s.push('0').index(i) == '0'
    ) by {
      assert(s.push('0').len() == s.len() + 1);
      assert(forall |i: int|
        0 <= i && i < s.len() as int ==> s.push('0').index(i) == s.index(i)
      ) by { }
      assert(s.push('0').index(s.len() as int) == '0');
    }
  }
}

proof fn lemma_all_zero_subrange_prefix(s: Seq<char>, m: int)
  requires
    AllZero(s),
    0 <= m && m <= s.len() as int
  ensures
    AllZero(s.subrange(0, m))
{
  if m == 0 {
    let t = s.subrange(0, 0);
    assert(t.len() == 0);
  } else {
    assert(m > 0);
    // Since m <= s.len(), s is non-empty
    assert(s.len() > 0);
    assert(forall |i: int| 0 <= i && i < s.len() as int ==> s
// </vc-code>

fn main() {}
}