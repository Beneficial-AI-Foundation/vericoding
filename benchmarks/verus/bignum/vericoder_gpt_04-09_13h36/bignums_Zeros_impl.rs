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
  assert(forall |i: int|
    0 <= i && i < s.len() as int ==> #[trigger] (s.index(i) == '0' || s.index(i) == '1')
  ) by {
    if s.len() == 0 {
      // vacuously true
    } else {
      assert(s.len() != 0);
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
    assert(forall |i: int| 0 <= i && i < s.len() as int ==> s.index(i) == '0');
    assert(s.push('0').len() == s.len() + 1);
    assert(forall |i: int|
      0 <= i && i < s.push('0').len() as int ==> #[trigger] s.push('0').index(i) == '0'
    ) by {
      assert(forall |i: int|
        0 <= i && i < s.len() as int ==> s.push('0').index(i) == s.index(i)
      );
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
    if s.len() == 0 {
      // impossible since m > 0 and m <= s.len()
      assert(false);
    } else {
      assert(s.len() != 0);
    }
    assert(forall |i: int|
      0 <= i && i < s.len() as int ==> s.index(i) == '0'
    ) by {
      // from AllZero(s) and s.len() != 0
    }
    assert(forall |i: int|
      0 <= i && i < m ==> #[trigger] s.subrange(0, m).index(i) == s.index(i)
    );
    assert(forall |i: int|
      0 <= i && i < s.subrange(0, m).len() as int ==> #[trigger] s.subrange(0, m).index(i) == '0'
    ) by {
      assert(s.subrange(0, m).len() == m as nat);
      assert(forall |i: int|
        0 <= i && i < m ==> s.subrange(0, m).index(i) == s.index(i)
      );
      assert(forall |i: int|
        0 <= i && i < m ==> s.index(i) == '0'
      );
    }
  }
}

proof fn lemma_all_zero_implies_str2int_zero(s: Seq<char>)
  requires
    AllZero(s)
  ensures
    Str2Int(s) == 0
  decreases
    s.len()
{
  lemma_all_zero_implies_valid(s);
  if s.len() == 0 {
    assert(Str2Int(s) == 0);
  } else {
    assert(s.len() > 0);
    assert(forall |i: int|
      0 <= i && i < s.len() as int ==> s.index(i) == '0'
    ) by {
      // from AllZero(s) and s.len() > 0
    }
    let m = s.len() as int - 1;
    lemma_all_zero_subrange_prefix(s, m);
    let p = s.subrange(0, m);
    lemma_all_zero_implies_valid(p);
    lemma_all_zero_implies_str2int_zero(p);
    assert(Str2Int(p) == 0);
    assert(s.index(m) == '0');
    assert(Str2Int(s) == 2 * Str2Int(p) + (if s.index(m) == '1' { 1nat } else { 0nat }));
    assert(Str2Int(s) == 2 * 0 + 0);
    assert(Str2Int(s) == 0);
  }
}
// </vc-helpers>

// <vc-spec>
exec fn Zeros(n: int) -> (s: Vec<char>)
  requires n >= 0
  ensures s@.len() == n as nat, ValidBitString(s@), Str2Int(s@) == 0, AllZero(s@)
// </vc-spec>
// <vc-code>
{
  let mut s: Vec<char> = Vec::new();
  let mut i: int = 0;
  while i < n
    invariant 0 <= i && i <= n
    invariant s@.len() == i as nat
    invariant AllZero(s@)
    decreases n - i
  {
    let old_seq = s@;
    proof { lemma_all_zero_push(old_seq); }
    s.push('0');
    assert(s@ == old_seq.push('0'));
    assert(AllZero(s@));
    i = i + 1;
  }
  proof { lemma_all_zero_implies_valid(s@); }
  proof { lemma_all_zero_implies_str2int_zero(s@); }
  s
}
// </vc-code>

fn main() {}
}