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
  // Str2Int(prefix + t) == Pow2(|t|) * Str2Int(prefix) + Str2Int(t)
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
      // s' == ""
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
    var last := if s[|s|-1] == '1' then 1 else 0;
    // Write s = first + rest
    var first := s[0];
    var rest := s[1..];
    // Use Str2IntConcat on first and rest (first is string of length 1)
    Str2IntConcat(first, rest);
    // first == "1"
    assert Str2Int(first) == 1;
    // Str2Int(s) == Pow2(|rest|) * 1 + Str2Int(rest)
    assert Str2Int(s) == Pow2(|s| - 1) + Str2Int(rest);
    // Str2Int(rest) >= 0
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
  // Handle case when s2 == "0" impossible because |s2|> |s1| >= 1
  if s1 == "0" {
    // s1 == "0" and |s2| > 1 so s2[0] != '0' (by normalization requirement)
    // Str2Int(s1) == 0
    assert Str2
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
ghost function Pow2(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
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
  // Str2Int(prefix + t) == Pow2(|t|) * Str2Int(prefix) + Str2Int(t)
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
      // s' == ""
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
    var last := if s[|s|-1] == '1' then 1 else 0;
    // Write s = first + rest
    var first := s[0];
    var rest := s[1..];
    // Use Str2IntConcat on first and rest (first is string of length 1)
    Str2IntConcat(first, rest);
    // first == "1"
    assert Str2Int(first) == 1;
    // Str2Int(s) == Pow2(|rest|) * 1 + Str2Int(rest)
    assert Str2Int(s) == Pow2(|s| - 1) + Str2Int(rest);
    // Str2Int(rest) >= 0
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
  // Handle case when s2 == "0" impossible because |s2|> |s1| >= 1
  if s1 == "0" {
    // s1 == "0" and |s2| > 1 so s2[0] != '0' (by normalization requirement)
    // Str2Int(s1) == 0
    assert Str2
// </vc-code>

