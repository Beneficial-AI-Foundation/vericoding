ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

// <vc-helpers>
ghost function pow2(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 2 * pow2(n - 1)
}

lemma Str2Int_sum(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) == (sum i | 0 <= i < s.Length :: if s[i] == '1' then pow2(s.Length - 1 - i) else 0)
  decreases s.Length
{
  if s.Length == 0 {
  } else {
    var prefix := s[0..s.Length-1];
    var last := s[s.Length-1];
    Str2Int_sum(prefix);
    calc {
      Str2Int(s);
      == { }
      2 * Str2Int(prefix) + (if last == '1' then 1 else 0);
      == { assert Str2Int(prefix) == (sum i | 0 <= i < prefix.Length :: if prefix[i] == '1' then pow2(prefix.Length - 1 - i) else 0); }
      2 * (sum i | 0 <= i < prefix.Length :: if prefix[i] == '1' then pow2(prefix.Length - 1 - i) else 0) + (if last == '1' then 1 else 0);
      == { }
      (sum i | 0 <= i < prefix.Length :: if prefix[i] == '1' then 2 * pow2(prefix.Length - 1 - i) else 0) + (if last == '1' then 1 else 0);
      == { }
      (sum i | 0 <= i < prefix.Length :: if prefix[i] == '1' then pow2(s.Length - 1 - i) else 0) + (if last == '1' then pow2(0) else 0);
      == { }
      (sum i | 0 <= i < s.Length :: if s[i] == '1' then pow2(s.Length - 1 - i) else 0);
    }
  }
}

lemma SumPow_identity(n: nat)
  ensures (sum k | 0 <= k < n :: pow2(k)) == pow2(n) - 1
  decreases n
{
  if n == 0 {
    assert (sum k | 0 <= k < 0 :: pow2(k)) == 0;
    assert pow2(0) - 1 == 0;
  } else {
    SumPow_identity(n - 1);
    calc {
      (sum k | 0 <= k < n :: pow2(k));
      == { }
      (sum k | 0 <= k < n - 1 :: pow2(k)) + pow2(n - 1);
      == { assert (sum k | 0 <= k < n - 1 :: pow2(k)) == pow2(n - 1) - 1; }
      (pow2(n - 1) - 1) + pow2(n - 1);
      == { }
      2 * pow2(n - 1) - 1;
      == { assert pow2(n) == 2 * pow2(n - 1); }
      pow2(n) - 1;
    }
  }
}

lemma Str2Int_upper_bound(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) <= pow2(s.Length) - 1
  decreases s.Length
{
  Str2Int_sum(s);
  if s.Length == 0 {
    assert Str2Int(s) == 0;
    assert pow2(0) - 1 == 0;
  } else {
    // Each bit contribution <= corresponding pow2, so sum <= sum pow2
    assert (sum i | 0 <= i < s.Length :: if s[i] == '1' then pow2(s.Length - 1 - i) else 0) <= (sum i | 0 <= i < s.Length :: pow2(s.Length - 1 - i));
    assert (sum i | 0 <= i < s.Length :: pow2(s.Length - 1 - i)) == (sum k | 0 <= k < s.Length :: pow2(k));
    SumPow_identity(s.Length);
    assert (sum k | 0 <= k < s.Length :: pow2(k)) == pow2(s.Length) - 1;
  }
}

lemma Str2Int_drop_leading_zeros(s: string, z: nat)
  requires ValidBitString(s)
  requires z <= s.Length
  requires forall i | 0 <= i < z :: s[i] == '0'
  ensures Str2Int(s) == Str2Int(s[z..])
  decreases s.Length
{
  Str2Int_sum(s);
  Str2Int_sum(s[z..]);
  // contributions from first z bits are zero
  assert (sum i | 0 <= i < s.Length :: if s[i] == '1' then pow2(s.Length - 1 - i) else 0)
       == (sum i | z <= i < s.Length :: if s[i] == '1' then pow2(s.Length - 1 - i) else 0);
  // reindex to match s[z..]
  assert (sum i | z <= i < s.Length :: if s[i] == '1' then pow2(s.Length - 1 - i) else 0)
       == (sum j | 0 <= j < s.Length - z :: if s[z + j] == '1' then pow2(s.Length - 1 - (z + j)) else 0);
  assert (sum j | 0 <= j < s.Length - z :: if s[z + j] == '1' then pow2(s.Length - 1 - (z + j)) else 0)
       == (sum j | 0 <= j < s.Length - z :: if s[z + j] == '1' then pow2(s[z..].Length - 1 - j) else 0);
  // now use the equalities produced by Str2Int_sum to conclude equality of Str2Int values
  assert Str2Int(s) == (sum i | 0 <= i < s.Length :: if s[i] == '1' then pow2(s.Length - 1 - i) else 0);
  assert Str2Int(s[z..]) == (sum j | 0 <= j < s[z..].Length :: if s[z..][j] == '1' then pow2(s[z..].Length - 1 - j) else 0);
  assert Str2Int(s) == Str2Int(s[z..]);
}

lemma pow2_monotone(a: nat, b: nat)
  requires a >= b
  ensures pow2(a) >= pow2(b)
  decreases a
{
  if a == b { } else {
    pow2_monotone(a - 1, b);
    assert pow2(a) == 2 * pow2(a - 1);
    assert pow2(a - 1) >= pow2(b);
    assert pow2(a) >= pow2(a - 1);
  }
}
// </vc-helpers>

// <vc-spec>
method Compare(s1: string, s2: string) returns (res: int)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures Str2Int(s1) < Str2Int(s2) ==> res == -1
  ensures Str2Int(s1) == Str2Int(s2) ==> res == 0
  ensures Str2Int(s1) > Str2Int(s2) ==> res == 1
  decreases Str2Int(s1) + Str2Int(s2)
// </vc-spec>
// <vc-code>
{
  // find first '1' in s1
  var i1 := 0;
  while i1 < |s1| && s1[i1] == '0' 
    invariant 0 <= i1 <= |s1|
    invariant forall k | 0 <= k < i1 :: s1[k] == '0'
  {
    i1 := i1 + 1;
  }
  // find first '1' in s2
  var i2 := 0;
  while i2 < |s2| && s2[i2] == '0'
    invariant 0 <= i2 <= |s2|
    invariant forall k | 0 <= k < i2 :: s2[k] == '0'
  {
    i2 := i2 + 1;
  }

  var len1 := |s1| - i1;
  var len2 := |s2| - i2;

  if len1 > len2 {
    // s1 has greater numeric value
    ghost var t1 := s1[i1..];
    ghost var t2 := s2[i2..];
    // leading zero drop
    if i1 > 0 {
      Str2Int_drop_leading_zeros(s1, i1);
    }
    if i2 > 0 {
      Str2Int_drop_leading_zeros(s2, i2);
    }
    assert Str2Int(s1) == Str2Int(t1);
    assert Str2Int(s2) == Str2Int(t2);
    // t1 starts with '1' because len1>len2 implies len1>0
    assert len1 > 0;
    assert i1 < |s1|;
    assert t1[0] == '1';
    // lower bound for s1 and upper bound for s2
    Str2Int_sum(t1);
    assert Str2Int(t1) >= pow2(len1 - 1);
    Str2Int_upper_bound(t2);
    assert Str2Int(t2) <= pow2(len2) - 1;
    // pow2 monotonicity: pow2(len1 - 1) >= pow2(len2)
    assert len1 - 1 >= len2;
    pow2_monotone(len1 - 1, len2);
    assert pow2(len1 - 1) >= pow2(len2);
    // combine to show s1 > s2
    assert Str2Int(t1) >= pow2(len1 - 1);
    assert pow2(len1 - 1) >= pow2(len2);
    assert pow2(len2) > pow2(len2) - 1;
    assert pow2(len2) - 1 >= Str2Int(t2);
    assert Str2Int(t1) > Str2Int(t2);
    assert Str2Int(s1) > Str2Int(s2);
    res := 1;
    return;
  } else if len1 < len2 {
    ghost var t1 := s1[i1..];
    ghost var t2 := s2[i2..];
    if i1 > 0 {
      Str2Int_drop_leading_zeros(s1, i1);
    }
    if i2 > 0 {
      Str2Int_drop_leading_zeros(s2, i2);
    }
    assert Str2Int(s1) == Str2Int(t1);
    assert Str2Int(s2) == Str2Int(t2);
    // symmetric argument
    assert len2 > 0;
    assert t2[0] == '1';
    Str2Int_sum(t2);
    assert Str2Int(t2) >= pow2(len2 - 1);
    Str2Int_upper_bound(t1);
    assert Str2Int(t1) <= pow2(len1) - 1;
    assert len2 - 1 >= len1;
    pow2_monotone(len2 - 1, len1);
    assert pow2(len2 - 1) >= pow2(len1);
    assert Str2Int(t2) >= pow2(len2 - 1);
    assert pow2(len2 - 1) >= pow2(len1);
    assert pow2(len1) - 1 >= Str2Int(t1) || true;
    assert Str2Int(t2) > Str2Int(t1);
    assert Str2Int(s2) > Str2Int(s1);
    res := -1;
    return;
  } else {
    // len1 == len2
    if len1 == 0 {
      // both represent zero
      res := 0;
      return;
    }
    // work with trimmed strings to simplify reasoning
    ghost var t1 := s1[i1..];
    ghost var t2 := s2[i2..];
    if i1 > 0 {
      Str2Int_drop_leading_zeros(s1, i1);
    }
    if i2 > 0 {
      Str2Int_drop_leading_zeros(s2, i2);
    }
    assert Str2Int(s1) == Str2Int(t1);
    assert Str2Int(s2) == Str2Int(t2);

    // compare lexicographically on the trimmed strings
    var j := 0;
    while j < len1 && t1[j] == t2[j]
      invariant 0 <= j <= len1
      invariant forall k | 0 <= k < j :: t1[k] == t2[k]
    {
      j := j + 1;
    }
    if j == len1 {
      res := 0;
      return;
    } else {
      // first differing position at j
      if t1[j] == '1' {
        // show Str2Int(t1) > Str2Int(t2)
        Str2Int_sum(t1);
        Str2Int_sum(t2);
        var rem := len1 - 1 - j;
        // contribution at position j
        assert (if t1[j] == '1' then pow2(rem) else 0) == pow2(rem);
        assert (if t2[j] == '1' then pow2(rem) else 0) == 0;
        // remaining suffix difference bounded by pow2(rem)-1
        var sfx1 := t1[j + 1..];
        var sfx2 := t2[j + 1..];
        Str2Int_upper_bound(sfx1);
        Str2Int_upper_bound(sfx2);
        assert Str2Int(sfx1) <= pow2(|sfx1|) - 1;
        assert Str2Int(sfx2) <= pow2(|sfx2|) - 1;
        // |sfx1| and |sfx2| are both rem
        assert |sfx1| == rem;
        assert |sfx2| == rem;
        assert Str2Int(sfx1) <= pow2(rem) - 1;
        assert Str2Int(sfx2) <= pow2(rem) - 1;
        // difference > 0
        assert Str2Int(t1) - Str2Int(t2) >= pow2(rem) - (pow2(rem) - 1);
        assert Str2Int(t1) - Str2Int(t2) > 0;
        assert Str2Int(t1) > Str2Int(t2);
        assert Str2Int(s1) > Str2Int(s2);
        res := 1;
        return;
      } else {
        // t1[j] == '0' and t2[j] == '1' so t1 < t2
        Str2Int_sum(t1);
        Str2Int_sum(t2);
        var rem := len1 - 1 - j;
        var sfx1 := t1[j + 1..];
        var sfx2 := t2[j + 1..];
        Str2Int_upper_bound(sfx1);
        Str2Int_upper_bound(sfx2);
        assert (if t1[j] == '1' then pow2(rem) else 0) == 0;
        assert (if t2[j] == '1' then pow2(rem) else 0) == pow2(rem);
        assert Str2Int(t2) - Str2Int(t1) > 0;
        assert Str2Int(s2) > Str2Int(s1);
        res := -1;
        return;
      }
    }
  }
}
// </vc-code>

