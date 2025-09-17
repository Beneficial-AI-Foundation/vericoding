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
  let mut v = Vec::new();
  let mut leading_zeros = true;
  for i in 0..s.len() {
    if leading_zeros && s[i] == '0' {
      continue;
    }
    leading_zeros = false;
    v.push(s[i]);
  }
  if v.len() == 0 {
    v.push('0');
  }
  v
}
// </vc-code>

// <vc-helpers>
proof fn lemma_unequal_length_comparison(s1: Seq<char>, s2: Seq<char>)
  requires
    ValidBitString(s1),
    ValidBitString(s2),
    s1.len() > 0,
    (s1.len() > 1 ==> s1.index(0) != '0'),
    s2.len() > 0,
    (s2.len() > 1 ==> s2.index(0) != '0'),
    s1.len() > s2.len(),
  ensures
    Str2Int(s1) > Str2Int(s2),
{
  if s1.len() == s2.len() + 1 {
    assert(Str2Int(s1) >= 2 * Str2Int(s2))
      by (nonlinear_arith)
      requires ValidBitString(s1), ValidBitString(s2), s1.len() == s2.len() + 1, s2.len() > 0, Str2Int(s2) >= 1
    ;
    assert(Str2Int(s1) > Str2Int(s2));
  } else {
    let s_prefix = s1.subrange(0, s1.len() as int - 1);
    lemma_unequal_length_comparison(s_prefix, s2);
    assert(Str2Int(s_prefix) > 0);
    assert(Str2Int(s1) >= 2 * Str2Int(s_prefix));
    assert(Str2Int(s1) > Str2Int(s2));
  }
}

proof fn lemma_compare_equal_length(s1: Seq<char>, s2: Seq<char>)
  requires
    ValidBitString(s1),
    ValidBitString(s2),
    s1.len() == s2.len(),
    s1.len() > 0,
  ensures
    Str2Int(s1) < Str2Int(s2) || Str2Int(s1) == Str2Int(s2) || Str2Int(s1) > Str2Int(s2),
    (forall |i: int|
       0 <= i && i < s1.len() ==> s1.index(i) == s2.index(i))
      ==>
      Str2Int(s1) == Str2Int(s2),
    (! (forall |i: int|
       0 <= i && i < s1.len() ==> s1.index(i) == s2.index(i)))
      ==>
      (exists |k: int|
         0 <= k && k < s1.len() && (forall |j: int|
           0 <= j && j < k ==> s1.index(j) == s2.index(j)) && s1.index(k) != s2.index(k)),
    (
      exists |k: int|
        0 <= k && k < s1.len() && (forall |j: int|
          0 <= j && j < k ==> s1.index(j) == s2.index(j)) && s1.index(k) == '0' && s2.index(k) == '1'
    )
      ==>
      Str2Int(s1) < Str2Int(s2),
    (
      exists |k: int|
        0 <= k && k < s1.len() && (forall |j: int|
          0 <= j && j < k ==> s1.index(j) == s2.index(j)) && s1.index(k) == '1' && s2.index(k) == '0'
    )
      ==>
      Str2Int(s1) > Str2Int(s2),
{
  let n = s1.len();
  if n == 0 {
    assert(Str2Int(s1) == 0 && Str2Int(s2) == 0);
    assert(Str2Int(s1) == Str2Int(s2));
  } else {
    let k = 0;
    while k < n
      invariant
        0 <= k && k <= n,
        s1.len() == n,
        s2.len() == n,
        ValidBitString(s1),
        ValidBitString(s2),
        (forall |j: int| 0 <= j && j < k ==> s1.index(j) == s2.index(j)),
    {
      if s1.index(k) != s2.index(k) {
        if s1.index(k) == '0' && s2.index(k) == '1' {
          let s1_suffix = s1.subrange(k as int, n as int);
          let s2_suffix = s2.subrange(k as int, n as int);
          let val1_suffix = Str2Int(s1_suffix);
          let val2_suffix = Str2Int(s2_suffix);
          assert(val1_suffix < val2_suffix)
            by (nonlinear_arith)
            requires s1_suffix.index(0) == '0', s2_suffix.index(0) == '1', ValidBitString(s1_suffix), ValidBitString(s2_suffix)
          ;
          assert(Str2Int(s1) < Str2Int(s2))
            by (nonlinear_arith)
            requires Str2Int(s1.subrange(0, k)) == Str2Int(s2.subrange(0, k)), val1_suffix < val2_suffix,
            Str2Int(s1) == Str2Int(s1.subrange(0, k)) * pow2(n - k) + val1_suffix,
            Str2Int(s2) == Str2Int(s2.subrange(0, k)) * pow2(n - k) + val2_suffix
          ;
        } else { // s1.index(k) == '1' && s2.index(k) == '0'
          let s1_suffix = s1.subrange(k as int, n as int);
          let s2_suffix = s2.subrange(k as int, n as int);
          let val1_suffix = Str2Int(s1_suffix);
          let val2_suffix = Str2Int(s2_suffix);
          assert(val1_suffix > val2_suffix)
            by (nonlinear_arith)
            requires s1_suffix.index(0) == '1', s2_suffix.index(0) == '0', ValidBitString(s1_suffix), ValidBitString(s2_suffix)
          ;
          assert(Str2Int(s1) > Str2Int(s2))
            by (nonlinear_arith)
            requires Str2Int(s1.subrange(0, k)) == Str2Int(s2.subrange(0, k)), val1_suffix > val2_suffix,
            Str2Int(s1) == Str2Int(s1.subrange(0, k)) * pow2(n - k) + val1_suffix,
            Str2Int(s2) == Str2Int(s2.subrange(0, k)) * pow2(n - k) + val2_suffix
          ;
        }
        return;
      }
      k = k + 1;
    }
    // If loop finishes, s1 == s2
    assert(Str2Int(s1) == Str2Int(s2));
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
  let t1 = NormalizeBitString(s1);
  let t2 = NormalizeBitString(s2);

  if t1.len() < t2.len() {
    return -1;
  } else if t1.len() > t2.len() {
    return 1;
  } else {
    // Lengths are equal, compare digit by digit from most significant
    let mut i = 0;
    while i < t1.len()
      invariant
        0 <= i && i <= t1.len(),
        t1.len() == t2.len(),
        ValidBitString(t1@),
        ValidBitString(t2@),
        Str2Int(t1@.subrange(0, i as int)) == Str2Int(t2@.subrange(0, i as int)),
    {
      if t1[i] < t2[i] {
        return -1;
      } else if t1[i] > t2[i] {
        return 1;
      }
      i = i + 1;
    }
    return 0;
  }
}
// </vc-code>

fn main() {}
}


