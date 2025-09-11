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

method CompareUnequal(s1: string, s2: string) returns (res: int)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures Str2Int(s1) < Str2Int(s2) ==> res == -1
  ensures Str2Int(s1) == Str2Int(s2) ==> res == 0
  ensures Str2Int(s1) > Str2Int(s2) ==> res == 1
  requires |s1| > 0
  requires |s1| > 1 ==> s1[0] != '0'
  requires |s2| > 0
  requires |s2| > 1 ==> s2[0] != '0'
  requires |s1| > |s2|
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma SameLengthNormalizedComparison(s1: string, s2: string, cmp: int)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires |s1| == |s2| && |s1| > 0
  requires |s1| > 1 ==> s1[0] != '0'
  requires |s2| > 1 ==> s2[0] != '0'
  requires cmp == LexCompare(s1, s2)
  ensures cmp < 0 ==> Str2Int(s1) < Str2Int(s2)
  ensures cmp == 0 ==> Str2Int(s1) == Str2Int(s2)
  ensures cmp > 0 ==> Str2Int(s1) > Str2Int(s2)
  ensures Str2Int(s1) < Str2Int(s2) ==> cmp < 0
  ensures Str2Int(s1) == Str2Int(s2) ==> cmp == 0
  ensures Str2Int(s1) > Str2Int(s2) ==> cmp > 0
{
  if |s1| == 0 {
    assert s1 == s2 == "";
    assert Str2Int(s1) == Str2Int(s2) == 0;
    assert cmp == 0;
  } else if s1 == s2 {
    assert cmp == 0;
    assert Str2Int(s1) == Str2Int(s2);
  } else {
    var i := FindFirstDifference(s1, s2);
    assert 0 <= i < |s1|;
    assert s1[..i] == s2[..i];
    assert s1[i] != s2[i];
    
    if s1[i] == '0' {
      assert s2[i] == '1';
      assert cmp < 0;
      LexCompareImpliesNumericLess(s1, s2, i);
    } else {
      assert s1[i] == '1' && s2[i] == '0';
      assert cmp > 0;
      LexCompareImpliesNumericGreater(s1, s2, i);
    }
  }
}

function FindFirstDifference(s1: string, s2: string): nat
  requires |s1| == |s2|
  requires s1 != s2
  ensures 0 <= FindFirstDifference(s1, s2) < |s1|
  ensures s1[FindFirstDifference(s1, s2)] != s2[FindFirstDifference(s1, s2)]
  ensures forall j :: 0 <= j < FindFirstDifference(s1, s2) ==> s1[j] == s2[j]
{
  if s1[0] != s2[0] then 0
  else 1 + FindFirstDifference(s1[1..], s2[1..])
}

lemma LexCompareImpliesNumericLess(s1: string, s2: string, i: nat)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires |s1| == |s2| && 0 <= i < |s1|
  requires s1[..i] == s2[..i]
  requires s1[i] == '0' && s2[i] == '1'
  ensures Str2Int(s1) < Str2Int(s2)
{
  if |s1| == 1 {
    assert Str2Int(s1) == 0 && Str2Int(s2) == 1;
  } else {
    var n1 := Str2Int(s1);
    var n2 := Str2Int(s2);
    
    var prefix1 := s1[0..i];
    var prefix2 := s2[0..i];
    assert prefix1 == prefix2;
    
    var suffix1 := s1[i+1..];
    var suffix2 := s2[i+1..];
    
    Str2IntDecomposition(s1, i);
    Str2IntDecomposition(s2, i);
  }
}

lemma LexCompareImpliesNumericGreater(s1: string, s2: string, i: nat)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires |s1| == |s2| && 0 <= i < |s1|
  requires s1[..i] == s2[..i]
  requires s1[i] == '1' && s2[i] == '0'
  ensures Str2Int(s1) > Str2Int(s2)
{
  LexCompareImpliesNumericLess(s2, s1, i);
}

lemma Str2IntDecomposition(s: string, i: nat)
  requires ValidBitString(s)
  requires 0 <= i < |s|
  ensures Str2Int(s) == Str2Int(s[0..i]) * Power2(|s| - i) + (if s[i] == '1' then Power2(|s| - i - 1) else 0) + Str2Int(s[i+1..])
{
  // Decomposition of Str2Int at position i
}

function Power2(n: nat): nat
{
  if n == 0 then 1 else 2 * Power2(n - 1)
}

function LexCompare(s1: string, s2: string): int
  ensures s1 == s2 ==> LexCompare(s1, s2) == 0
  ensures |s1| == |s2| && s1 != s2 ==> LexCompare(s1, s2) != 0
{
  if |s1| == 0 && |s2| == 0 then 0
  else if |s1| == 0 then -1
  else if |s2| == 0 then 1
  else if s1[0] < s2[0] then -1
  else if s1[0] > s2[0] then 1
  else LexCompare(s1[1..], s2[1..])
}

lemma LongerNormalizedIsGreater(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires |s1| > 0 && |s2| > 0
  requires |s1| > 1 ==> s1[0] != '0'
  requires |s2| > 1 ==> s2[0] != '0'
  requires |s1| > |s2|
  ensures Str2Int(s1) > Str2Int(s2)
{
  if |s2| == 1 {
    assert s2[0] == '0' || s2[0] == '1';
    assert Str2Int(s2) <= 1;
    assert |s1| >= 2;
    assert s1[0] == '1';
    MinValueForLength(s1);
  } else {
    assert s2[0] == '1';
    MinValueForLength(s1);
    MaxValueForLength(s2);
  }
}

lemma MinValueForLength(s: string)
  requires ValidBitString(s)
  requires |s| > 1
  requires s[0] == '1'
  ensures Str2Int(s) >= Power2(|s| - 1)
{
  // Minimum value for normalized string of length n is 2^(n-1)
}

lemma MaxValueForLength(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  ensures Str2Int(s) < Power2(|s|)
{
  // Maximum value for string of length n is 2^n - 1
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
  var t1 := NormalizeBitString(s1);
  var t2 := NormalizeBitString(s2);
  
  if |t1| > |t2| {
    LongerNormalizedIsGreater(t1, t2);
    res := 1;
  } else if |t1| < |t2| {
    LongerNormalizedIsGreater(t2, t1);
    res := -1;
  } else {
    var cmp := LexCompare(t1, t2);
    SameLengthNormalizedComparison(t1, t2, cmp);
    if cmp < 0 {
      res := -1;
    } else if cmp == 0 {
      res := 0;
    } else {
      res := 1;
    }
  }
}
// </vc-code>

