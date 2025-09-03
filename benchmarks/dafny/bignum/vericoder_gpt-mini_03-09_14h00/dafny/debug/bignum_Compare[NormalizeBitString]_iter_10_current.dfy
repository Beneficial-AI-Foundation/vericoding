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

method NormalizeBitString(s: string) returns(t: string)
  // Remove leading zeros, except keep at least one digit
  ensures ValidBitString(t)
  // I added and proved some extra post-conditions:
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(s) == Str2Int(t)
{
  assume{:axiom} false;
}

// <vc-helpers>
ghost function Pow2(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

lemma Pow2Mono(a: nat, b: nat)
  requires a <= b
  ensures Pow2(a) <= Pow2(b)
  decreases b - a
{
  if a == b {
    assert Pow2(a) == Pow2(b);
  } else {
    assert Pow2(b) == 2 * Pow2(b - 1);
    Pow2Mono(a, b - 1);
    assert Pow2(a) <= Pow2(b - 1);
    assert Pow2(a) <= 2 * Pow2(b - 1);
    assert Pow2(a) <= Pow2(b);
  }
}

lemma Str2IntConcat(x: string, y: string)
  requires ValidBitString(x) && ValidBitString(y)
  ensures Str2Int(x + y) == Pow2(|y|) * Str2Int(x) + Str2Int(y)
  decreases |y|
{
  if |y| == 0 {
    assert x + y == x;
    assert Pow2(0) == 1;
    assert Str2Int(x + y) == Str2Int(x);
    assert Str2Int(y) == 0;
    assert Str2Int(x) == Pow2(0) * Str2Int(x) + Str2Int(y);
  } else {
    var y' := y[..|y|-1];
    var last := if y[|y|-1] == '1' then 1 else 0;
    Str2IntConcat(x, y');
    assert Str2Int(x + y) == 2 * Str2Int((x + y)[0..|x + y| - 1]) + (if (x + y)[|x + y| - 1] == '1' then 1 else 0);
    assert (x + y)[0..|x + y| - 1] == x + y';
    assert (x + y)[|x + y| - 1] == y[|y| - 1];
    assert Str2Int(x + y) == 2 * Str2Int(x + y') + last;
    assert Str2Int(y) == 2 * Str2Int(y') + last;
    assert Pow2(|y|) == 2 * Pow2(|y'|);
    var mid := 2 * Pow2(|y'|) * Str2Int(x) + 2 * Str2Int(y') + last;
    assert Str2Int(x + y) == mid;
    assert Pow2(|y|) * Str2Int(x) + Str2Int(y) == mid;
    assert Str2Int(x + y) == Pow2(|y|) * Str2Int(x) + Str2Int(y);
  }
}

lemma Str2IntZeros(s: string)
  requires ValidBitString(s)
  requires forall i | 0 <= i < |s| :: s[i] == '0'
  ensures Str2Int(s) == 0
  decreases |s|
{
  if |s| == 0 {
    assert Str2Int(s) == 0;
  } else {
    var s' := s[..|s|-1];
    Str2IntZeros(s');
    assert Str2Int(s) == 2 * Str2Int(s') + 0;
    assert Str2Int(s') == 0;
    assert Str2Int(s) == 0;
  }
}

lemma RemoveLeadingZerosEquality(prefix: string, t: string)
  requires ValidBitString(prefix) && ValidBitString(t)
  requires forall i | 0 <= i < |prefix| :: prefix[i] == '0'
  ensures Str2Int(prefix + t) == Str2Int(t)
  decreases |prefix|
{
  Str2IntConcat(prefix, t);
  Str2IntZeros(prefix);
  assert Pow2(|t|) * Str2Int(prefix) + Str2Int(t) == Str2Int(t);
  assert Str2Int(prefix + t) == Str2Int(t);
}

lemma Str2IntUpperBound(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) <= if |s| == 0 then 0 else Pow2(|s|) - 1
  decreases |s|
{
  if |s| == 0 {
    assert Str2Int(s) == 0;
  } else {
    var s' := s[..|s|-1];
    var last := if s[|s|-1] == '1' then 1 else 0;
    Str2IntUpperBound(s');
    assert Str2Int(s) == 2 * Str2Int(s') + last;
    if |s'| == 0 {
      assert Str2Int(s') == 0;
      assert Str2Int(s) <= 2 * 0 + 1;
      assert Pow2(|s|) - 1 == 2 * Pow2(|s'|) - 1;
      assert Str2Int(s) <= Pow2(|s|) - 1;
    } else {
      assert Str2Int(s') <= Pow2(|s'|) - 1;
      assert 2 * Str2Int(s') + last <= 2 * (Pow2(|s'|) - 1) + 1;
      assert 2 * (Pow2(|s'|) - 1) + 1 == 2 * Pow2(|s'|) - 1;
      assert 2 * Pow2(|s'|) - 1 == Pow2(|s|) - 1;
      assert Str2Int(s) <= Pow2(|s|) - 1;
    }
  }
}

lemma Str2IntLowerBoundFirstOne(s: string)
  requires ValidBitString(s)
  requires |s| > 0 && s[0] == '1'
  ensures Str2Int(s) >= Pow2(|s| - 1)
  decreases |s|
{
  if |s| == 1 {
    assert Str2Int(s) == 1;
    assert Pow2(0) == 1;
  } else {
    var s' := s[..|s|-1];
    var rest := s[1..];
    Str2IntConcat(s[0..1], rest);
    assert Str2Int(s[0..1]) == (if s[0] == '1' then 1 * Pow2(1 - 1) + (if s[1] == '1' then 1 else 0) else 0);
    // Use Str2IntConcat on first and rest (first is string of length 1)
    Str2IntConcat(s[0..1], rest);
    assert Str2Int(s) == Pow2(|rest|) * Str2Int(s[0..1]) + Str2Int(rest);
    assert Str2Int(s[0..1]) >= 1; // since s[0] == '1'
    assert Str2Int(s) >= Pow2(|rest|) * 1;
    assert Pow2(|rest|) == Pow2(|s| - 1);
    assert Str2Int(s) >= Pow2(|s| - 1);
  }
}

lemma LenLessImpliesNum(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires |s1| > 0 && |s2| > 0
  requires s1[0] != '0' || (|s1| == 1 && s1[0] == '0')
  requires s2[0] != '0' || (|s2| == 1 && s2[0] == '0')
  requires |s1| < |s2|
  ensures Str2Int(s1) < Str2Int(s2)
  decreases |s2|
{
  if s1 == "0" {
    // s1 == "0"
    Str2IntZeros(s1);
    assert Str2Int(s1) == 0;
    // s2 has length > |s1| = 1, so |s2| > 1, and by normalization s2[0] != '0'
    if |s2| == 1 {
      // cannot happen because |s1| < |s2| and |s1| == 1
      assert false;
    } else {
      // s2[0] != '0' and |s2| > 1
      Str2IntLowerBoundFirstOne(s2);
      assert Str2Int(s2) >= Pow2(|s2| - 1);
      assert 0 < Str2Int(s2);
    }
  } else {
    // s1 is not "0"
    Str2IntUpperBound(s1);
    Str2IntLowerBoundFirstOne(s2);
    assert Str2Int(s1) <= Pow2(|s1|) - 1;
    assert Str2Int(s2) >= Pow2(|s2| - 1);
    // Since |s1| < |s2| we have |s1| <= |s2| - 1
    assert |s1| <= |s2| - 1;
    Pow2Mono(|s1|, |s2| - 1);
    assert Pow2(|s1|) <= Pow2(|s2| - 1);
    assert Pow2(|s1|) - 1 < Pow2(|s2| - 1);
    assert Str2Int(s1) <= Pow2(|s1|) - 1;
    assert Str2Int(s1) < Pow2(|s2| - 1) <= Str2Int(s2);
    assert Str2Int(s1) < Str2Int(s2);
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
  // Find first non-zero (i.e., first '1') in s1
  var i1 := 0;
  while i1 < |s1| && s1[i1] == '0'
    invariant 0 <= i1 <= |s1|
    invariant forall j | 0 <= j < i1 :: s1[j] == '0'
    decreases |s1| - i1
  {
    i1 := i1 + 1;
  }
  // Find first non-zero in s2
  var i2 := 0;
  while i2 < |s2| && s2[i2] == '0'
    invariant 0 <= i2 <= |s2|
    invariant forall j | 0 <= j < i2 :: s2[j] == '0'
    decreases |s2| - i2
  {
    i2 := i2 + 1;
  }

  var t1 := if i1 == |s1| then "0" else s1[i1..];
  var t2 := if i2 == |s2| then "0" else s2[i2..];

  // Connect original strings to their normalized versions
  var p1 := s1[..i1];
  var p2 := s2[..i2];
  // p1 and p2 satisfy the "all zeros" property by loop invariants
  RemoveLeadingZerosEquality(p1, t1);
  RemoveLeadingZerosEquality(p2, t2);
  // Now Str2Int(s1) == Str2Int(t1) and Str2Int(s2) == Str2Int(t2)

  if |t1| < |t2| {
    // normalized strings: either start with '1' or are "0" of length 1
    LenLessImpliesNum(t1, t2);
    // Using equalities above, conclude comparison
    assert Str2Int(s1) < Str2Int(s2);
    res := -1;
    return;
  } else if |t1| > |t2| {
    LenLessImpliesNum(t2, t1);
    assert Str2Int(s2) < Str2Int(s1);
    res := 1;
    return;
  } else {
    // Equal lengths: compare lexicographically
    var j := 0;
    while j < |t1| && t1[j] == t2[j]
      invariant 0 <= j <= |t1|
      decreases |t1| - j
    {
      j := j + 1;
    }
    if j == |t1| {
      // identical strings
      assert Str2Int(t1) == Str2Int(t2);
      assert Str2Int(s1) == Str2Int(s2);
      res := 0;
      return;
    } else {
      // first differing bit at j
      // Let suffixes starting at j
      var sfx1 := t1[j..];
      var sfx2 := t2[j..];
      // prefix equal: t1[0..j] == t2[0..j]
      // Reduce comparison to suffixes
      Str2IntConcat(t1[0..j], sfx1);
      Str2IntConcat(t1[0..j], sfx2);
      // Now compare sfx1 and sfx2 which start with differing bits
      if sfx1[0] == '0' && sfx2[0] == '1' {
        // sfx1 = '0' + r1, sfx2 = '1' + r2
        var r1 := sfx1[1..];
        var r2 := sfx2[1..];
        // Str2Int(sfx1) == Str2Int(r1)
        Str2IntConcat("0", r1);
        Str2IntConcat("1", r2);
        Str2IntUpperBound(r1);
        // Str2Int(r1) <= Pow2(|r1|) - 1 < Pow2(|r1|) <= Pow2(|r1|) + Str2Int(r2) = Str2Int(sfx2)
        assert Str2Int(sfx1) == Str2Int(r1);
        assert Str2Int(sfx2) == Pow2(|r2|) + Str2Int(r2);
        // Pow2(|r1|) == Pow2(|r2|) because |r1| == |r2|
        assert |r1| == |r2|;
        assert Pow2(|r1|) == Pow2(|r2|);
        assert Str2Int(r1) <= Pow2(|r1|) - 1;
        assert Pow2(|r1|) - 1 < Pow2(|r1|);
        assert Pow2(|r1|) <= Pow2(|r1|) + Str2Int(r2);
        assert Str2Int(sfx1) < Str2Int(sfx2);
        // hence t1 < t2
        assert Str2Int(t1) < Str2Int(t2);
        assert Str2Int(s1) < Str2Int(s2);
        res := -1;
        return;
      } else {
        // sfx1[0] == '1' and sfx2[0] == '0'
        var r1 := sfx1[1..];
        var r2 := sfx2[1..];
        Str2IntConcat("1", r1);
        Str2IntConcat("0", r2);
        Str2IntUpperBound(r2);
        assert Str2Int(sfx2) == Str2Int(r2);
        assert Str2Int(sfx1) == Pow2(|r1|) + Str2Int(r1);
        assert Str2Int(sfx2) <= Pow2(|r2|) - 1;
        assert |r1| == |r2|;
        assert Pow2(|r2|) - 1 < Pow2(|r2|) + Str2Int(r1);
        assert Str2Int(sfx2) < Str2Int(sfx1);
        assert Str2Int(t2) < Str2Int(t1);
        assert Str2Int(s2) < Str2Int(s1);
        res := 1;
        return;
      }
    }
  }
}
// </vc-code>

