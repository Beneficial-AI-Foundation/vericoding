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
  /* code modified by LLM (iteration 4): normalize input by copying chars and stripping leading zeros */
  let mut t: Vec<char> = Vec::new();
  let mut idx: usize = 0;
  while idx < s.len()
      invariant
          0 <= idx as int && idx as int <= s.len() as int,
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
              1 <= t.len() as int,
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
  /* code modified by LLM (iteration 4): s1 longer than s2 and normalized, prove s1 > s2 and return 1 */
  proof {
      /* derive lower bound for s1 and upper bound for s2 */
      Str2Int_lower_bound(s1@);
      Str2Int_upper_bound(s2@);
      /* from preconditions s1@.len() > s2@.len() and s2@.len() > 0 we have s1@.len() > 1 */
      assert(s1@.len() > s2@.len());
      assert(s1@.len() - 1 >= s2@.len());
      /* monotonicity of TwoPow */
      TwoPow_monotone(s1@.len() - 1, s2@.len());
      /* combine bounds */
      assert(TwoPow(s1@.len() - 1) >= TwoPow(s2@.len()));
      assert(Str2Int(s1@) >= TwoPow(s1@.len() - 1));
      assert(Str2Int(s2@) <= TwoPow(s2@.len()) - 1);
      assert(Str2Int(s1@) > Str2Int(s2@));
  }
  1
}
// </vc-code>

// <vc-helpers>
/* helper modified by LLM (iteration 4): define TwoPow as 2^n */
spec fn TwoPow(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * TwoPow(n - 1) }
}

/* helper modified by LLM (iteration 4): monotonicity of TwoPow */
proof fn TwoPow_monotone(m: nat, n: nat)
    requires
        m >= n,
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

/* helper modified by LLM (iteration 4): Str2Int recursive decomposition for last bit */
proof fn Str2Int_subrange_last(s: Seq<char>, i: int)
    requires
        ValidBitString(s),
        0 <= i && i < s.len(),
    ensures
        Str2Int(s.subrange(0, i + 1)) == 2 * Str2Int(s.subrange(0, i)) + (if s.index(i) == '1' { 1nat } else { 0nat }),
{
    assert(Str2Int(s.subrange(0, i + 1)) == 2 * Str2Int(s.subrange(0, i)) + (if s.index(i) == '1' { 1nat } else { 0nat }));
}

/* helper modified by LLM (iteration 4): upper bound Str2Int(s) <= 2^{len}-1 */
proof fn Str2Int_upper_bound(s: Seq<char>)
    requires
        ValidBitString(s),
    ensures
        Str2Int(s) <= TwoPow(s.len()) - 1,
    decreases
        s.len()
{
    if s.len() == 0 {
        assert(Str2Int(s) == 0);
        assert(TwoPow(0) == 1);
    } else {
        let n: nat = s.len() - 1;
        Str2Int_subrange_last(s, n as int);
        Str2Int_upper_bound(s.subrange(0, n as int));
        assert(Str2Int(s.subrange(0, n as int)) <= TwoPow(n) - 1);
        assert(2 * Str2Int(s.subrange(0, n as int)) + (if s.index(n as int) == '1' { 1nat } else { 0nat }) <= 2 * (TwoPow(n) - 1) + 1);
        assert(2 * (TwoPow(n) - 1) + 1 == TwoPow(n + 1) - 1);
        assert(Str2Int(s) <= TwoPow(s.len()) - 1);
    }
}

/* helper modified by LLM (iteration 4): lower bound Str2Int(s) >= 2^{len-1} for normalized strings of length>1 */
proof fn Str2Int_lower_bound(s: Seq<char>)
    requires
        ValidBitString(s),
        s.len() > 1,
        s.index(0) != '0',
    ensures
        Str2Int(s) >= TwoPow(s.len() - 1),
    decreases
        s.len()
{
    if s.len() == 2 {
        assert(s.index(0) == '1');
        assert(Str2Int(s) >= TwoPow(1));
    } else {
        let n: nat = s.len() - 1;
        Str2Int_subrange_last(s, n as int);
        Str2Int_lower_bound(s.subrange(0, n as int));
        assert(Str2Int(s.subrange(0, n as int)) >= TwoPow(n - 1));
        assert(2 * Str2Int(s.subrange(0, n as int)) + (if s.index(n as int) == '1' { 1nat } else { 0nat }) >= 2 * TwoPow(n - 1));
        assert(2 * TwoPow(n - 1) == TwoPow(n));
        assert(Str2Int(s) >= TwoPow(s.len() - 1));
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
  /* code modified by LLM (iteration 4): normalize inputs and compare lengths/lexicographically */
  let t1 = NormalizeBitString(s1);
  let t2 = NormalizeBitString(s2);
  if t1.len() > t2.len() {
      CompareUnequal(t1.as_slice(), t2.as_slice())
  } else if t1.len() < t2.len() {
      -CompareUnequal(t2.as_slice(), t1.as_slice())
  } else {
      let mut i: usize = 0;
      while i < t1.len()
          invariant
              0 <= i as int && i as int <= t1.len() as int,
          decreases t1.len() as int - i as int
      {
          if t1[i] < t2[i] {
              return -1;
          } else if t1[i] > t2[i] {
              return 1;
          }
          i += 1;
      }
      0
  }
}
// </vc-code>

fn main() {}
}


