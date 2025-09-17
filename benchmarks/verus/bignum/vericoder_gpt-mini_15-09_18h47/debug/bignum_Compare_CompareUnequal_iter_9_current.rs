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
  /* code modified by LLM (iteration 9): compute integer value and produce minimal bit vector */
  let mut acc: nat = 0;
  let mut i: usize = 0usize;
  while i < s.len()
      invariant
          0 <= i as int && i as int <= s.len() as int,
          acc == Str2Int(s@.subrange(0, i as int)),
      decreases s.len() as int - i as int
  {
      let bit: nat = if s[i] == '1' { 1 } else { 0 };
      acc = 2 * acc + bit;
      i += 1usize;
  }

  if acc == 0 {
      let mut t: Vec<char> = Vec::new();
      t.push('0');
      proof {
          if ValidBitString(s@) {
              assert(Str2Int(s@) == acc);
              assert(Str2Int(t@) == 0);
              assert(Str2Int(s@) == Str2Int(t@));
          }
      }
      t
  } else {
      let mut bits: Vec<char> = Vec::new();
      let mut v: nat = acc;
      while v > 0
          invariant
              v >= 0,
          decreases v
      {
          if v % 2 == 1 { bits.push('1'); } else { bits.push('0'); }
          v = v / 2;
      }
      let mut t: Vec<char> = Vec::new();
      let mut j: usize = bits.len();
      while j > 0
          invariant
              0 <= j as int && j as int <= bits.len() as int,
          decreases j as int
      {
          j -= 1;
          t.push(bits[j]);
      }
      proof {
          if ValidBitString(s@) {
              assert(Str2Int(s@) == acc);
              assert(Str2Int(t@) == acc);
              assert(Str2Int(s@) == Str2Int(t@));
          }
      }
      t
  }
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
  /* code modified by LLM (iteration 9): prove longer normalized string has larger integer */
  proof {
      assert(s1@.len() > 0);
      assert(s2@.len() > 0);
      assert(s1@.len() > s2@.len());
      if s1@.len() > 1 {
          Str2Int_lower_bound(s1@);
          assert(Str2Int(s1@) >= TwoPow(s1@.len() as int - 1));
      } else {
          assert(Str2Int(s1@) >= 0);
      }
      Str2Int_upper_bound(s2@);
      assert(Str2Int(s2@) <= TwoPow(s2@.len() as int) - 1);
      let m: int = s1@.len() as int - 1;
      let n: int = s2@.len() as int;
      assert(m >= n);
      TwoPow_monotone(m, n);
      assert(TwoPow(m) >= TwoPow(n));
      assert(TwoPow(m) > TwoPow(n) - 1);
      assert(Str2Int(s1@) >= TwoPow(m));
      assert(Str2Int(s2@) <= TwoPow(n) - 1);
      assert(Str2Int(s1@) > Str2Int(s2@));
  }
  1
}
// </vc-code>

// <vc-helpers>
/* helper modified by LLM (iteration 9): TwoPow is 2^n for integer n (nonpositive maps to 1) */
spec fn TwoPow(n: int) -> nat
    decreases
        if n > 0 { n } else { 0 }
{
    if n <= 0 { 1 } else { 2 * TwoPow(n - 1) }
}

/* helper modified by LLM (iteration 9): monotonicity of TwoPow for nonnegative ints */
proof fn TwoPow_monotone(m: int, n: int)
    requires
        m >= n,
        n >= 0,
    ensures
        TwoPow(m) >= TwoPow(n),
    decreases
        m - n
{
    if m == n {
    } else {
        assert(m > n);
        TwoPow_monotone(m - 1, n);
        assert(TwoPow(m) == 2 * TwoPow(m - 1));
        assert(TwoPow(m - 1) >= TwoPow(n));
        assert(2 * TwoPow(m - 1) >= TwoPow(n));
    }
}

/* helper modified by LLM (iteration 9): decomposition of Str2Int for subrange ending at i */
proof fn Str2Int_subrange_last(s: Seq<char>, i: int)
    requires
        ValidBitString(s),
        0 <= i && i < s.len(),
    ensures
        Str2Int(s.subrange(0, i + 1)) == 2 * Str2Int(s.subrange(0, i)) + (if s.index(i) == '1' { 1 } else { 0 }),
{
    assert(Str2Int(s.subrange(0, i + 1)) == 2 * Str2Int(s.subrange(0, i)) + (if s.index(i) == '1' { 1 } else { 0 }));
}

/* helper modified by LLM (iteration 9): upper bound Str2Int(s) <= 2^{len}-1 */
proof fn Str2Int_upper_bound(s: Seq<char>)
    requires
        ValidBitString(s),
    ensures
        Str2Int(s) <= TwoPow(s.len() as int) - 1,
    decreases
        s.len()
{
    if s.len() == 0 {
        assert(Str2Int(s) == 0);
        assert(TwoPow(0) == 1);
    } else {
        let n: int = s.len() as int - 1;
        Str2Int_subrange_last(s, n);
        Str2Int_upper_bound(s.subrange(0, n));
        assert(Str2Int(s.subrange(0, n)) <= TwoPow(n) - 1);
        assert(2 * Str2Int(s.subrange(0, n)) + (if s.index(n) == '1' { 1 } else { 0 }) <= 2 * (TwoPow(n) - 1) + 1);
        assert(2 * (TwoPow(n) - 1) + 1 == TwoPow(n + 1) - 1);
        assert(Str2Int(s) <= TwoPow(s.len() as int) - 1);
    }
}

/* helper modified by LLM (iteration 9): lower bound Str2Int(s) >= 2^{len-1} for normalized strings (len>1 and first bit '1') */
proof fn Str2Int_lower_bound(s: Seq<char>)
    requires
        ValidBitString(s),
        s.len() > 1,
        s.index(0) != '0',
    ensures
        Str2Int(s) >= TwoPow(s.len() as int - 1),
    decreases
        s.len()
{
    if s.len() == 2 {
        assert(s.index(0) == '1');
        assert(Str2Int(s) >= TwoPow(1));
    } else {
        let n: int = s.len() as int - 1;
        Str2Int_subrange_last(s, n);
        Str2Int_lower_bound(s.subrange(0, n));
        assert(Str2Int(s.subrange(0, n)) >= TwoPow(n - 1));
        assert(2 * Str2Int(s.subrange(0, n)) + (if s.index(n) == '1' { 1 } else { 0 }) >= 2 * TwoPow(n - 1));
        assert(2 * TwoPow(n - 1) == TwoPow(n));
        assert(Str2Int(s) >= TwoPow(s.len() as int - 1));
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
  /* code modified by LLM (iteration 9): normalize inputs and compare by length and lexicographic order */
  let t1 = NormalizeBitString(s1);
  let t2 = NormalizeBitString(s2);
  if t1.len() > t2.len() {
      CompareUnequal(t1.as_slice(), t2.as_slice())
  } else if t1.len() < t2.len() {
      -CompareUnequal(t2.as_slice(), t1.as_slice())
  } else {
      let len = t1.len();
      let mut i: usize = 0usize;
      while i < len
          invariant
              0 <= i as int && i as int <= len as int,
          decreases len as int - i as int
      {
          if t1[i] == '0' && t2[i] == '1' {
              return -1;
          } else if t1[i] == '1' && t2[i] == '0' {
              return 1;
          }
          i += 1usize;
      }
      0
  }
}
// </vc-code>

fn main() {}
}


