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
lemma NormalizedComparison(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires |s1| > 0 && |s2| > 0
  requires |s1| > 1 ==> s1[0] != '0'
  requires |s2| > 1 ==> s2[0] != '0'
  ensures |s1| < |s2| ==> Str2Int(s1) < Str2Int(s2)
  ensures |s1| > |s2| ==> Str2Int(s1) > Str2Int(s2)
  ensures |s1| == |s2| ==> (Str2Int(s1) < Str2Int(s2) <==> LexicographicLess(s1, s2))
  ensures |s1| == |s2| ==> (Str2Int(s1) == Str2Int(s2) <==> s1 == s2)
  ensures |s1| == |s2| ==> (Str2Int(s1) > Str2Int(s2) <==> LexicographicLess(s2, s1))
{
  if |s1| < |s2| {
    LengthImpliesSmaller(s1, s2);
  } else if |s1| > |s2| {
    LengthImpliesSmaller(s2, s1);
  } else {
    SameLengthComparison(s1, s2);
  }
}

lemma LengthImpliesSmaller(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires |s1| > 0 && |s2| > 0
  requires |s1| < |s2|
  requires |s2| > 1 ==> s2[0] != '0'
  ensures Str2Int(s1) < Str2Int(s2)
{
  if |s2| == 1 {
    assert Str2Int(s2) <= 1;
    assert |s1| == 0;
    assert Str2Int(s1) == 0;
  } else {
    assert s2[0] != '0';
    assert s2[0] == '1';
    MinValueWithLeading1(s2);
    MaxValueBound(s1);
  }
}

lemma MinValueWithLeading1(s: string)
  requires ValidBitString(s)
  requires |s| >= 2
  requires s[0] == '1'
  ensures Str2Int(s) >= Power2(|s| - 1)
{
  if |s| == 2 {
    assert Str2Int(s) >= 2;
    assert Power2(1) == 2;
  } else {
    var prefix := s[0..|s|-1];
    assert prefix[0] == '1';
    MinValueWithLeading1(prefix);
    assert Str2Int(prefix) >= Power2(|prefix| - 1);
    assert Str2Int(s) == 2 * Str2Int(prefix) + (if s[|s|-1] == '1' then 1 else 0);
    assert Str2Int(s) >= 2 * Power2(|s| - 2);
    assert 2 * Power2(|s| - 2) == Power2(|s| - 1);
  }
}

lemma MaxValueBound(s: string)
  requires ValidBitString(s)
  requires |s| >= 0
  ensures Str2Int(s) < Power2(|s|)
{
  if |s| == 0 {
    assert Str2Int(s) == 0;
    assert Power2(0) == 1;
  } else {
    var prefix := s[0..|s|-1];
    MaxValueBound(prefix);
    assert Str2Int(prefix) < Power2(|prefix|);
    assert Str2Int(s) == 2 * Str2Int(prefix) + (if s[|s|-1] == '1' then 1 else 0);
    assert Str2Int(s) <= 2 * Str2Int(prefix) + 1;
    assert Str2Int(s) < 2 * Power2(|s| - 1);
    assert 2 * Power2(|s| - 1) == Power2(|s|);
  }
}

function Power2(n: nat): nat
{
  if n == 0 then 1 else 2 * Power2(n - 1)
}

predicate LexicographicLess(s1: string, s2: string)
  requires |s1| == |s2|
{
  exists i :: 0 <= i < |s1| && 
    (forall j :: 0 <= j < i ==> s1[j] == s2[j]) &&
    s1[i] < s2[i]
}

lemma SameLengthComparison(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires |s1| == |s2| > 0
  ensures Str2Int(s1) < Str2Int(s2) <==> LexicographicLess(s1, s2)
  ensures Str2Int(s1) == Str2Int(s2) <==> s1 == s2
  ensures Str2Int(s1) > Str2Int(s2) <==> LexicographicLess(s2, s1)
{
  if |s1| == 1 {
    assert Str2Int(s1) == (if s1[0] == '1' then 1 else 0);
    assert Str2Int(s2) == (if s2[0] == '1' then 1 else 0);
  } else {
    var p1 := s1[0..|s1|-1];
    var p2 := s2[0..|s2|-1];
    var d1 := if s1[|s1|-1] == '1' then 1 else 0;
    var d2 := if s2[|s2|-1] == '1' then 1 else 0;
    
    SameLengthComparison(p1, p2);
    
    if Str2Int(p1) < Str2Int(p2) {
      assert Str2Int(s1) == 2 * Str2Int(p1) + d1;
      assert Str2Int(s2) == 2 * Str2Int(p2) + d2;
      assert Str2Int(s1) < Str2Int(s2);
      assert LexicographicLess(p1, p2);
      assert LexicographicLess(s1, s2);
    } else if Str2Int(p1) > Str2Int(p2) {
      assert Str2Int(s1) > Str2Int(s2);
      assert LexicographicLess(p2, p1);
      assert LexicographicLess(s2, s1);
    } else {
      assert p1 == p2;
      assert Str2Int(s1) == 2 * Str2Int(p1) + d1;
      assert Str2Int(s2) == 2 * Str2Int(p2) + d2;
      
      if d1 < d2 {
        assert s1[|s1|-1] == '0' && s2[|s2|-1] == '1';
        assert LexicographicLess(s1, s2);
      } else if d1 > d2 {
        assert s1[|s1|-1] == '1' && s2[|s2|-1] == '0';
        assert LexicographicLess(s2, s1);
      } else {
        assert s1[|s1|-1] == s2[|s2|-1];
        assert s1 == s2;
      }
    }
  }
}

method LexicographicCompare(s1: string, s2: string) returns (res: int)
  requires |s1| == |s2|
  ensures res == -1 <==> LexicographicLess(s1, s2)
  ensures res == 0 <==> s1 == s2
  ensures res == 1 <==> LexicographicLess(s2, s1)
{
  var i := 0;
  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant forall j :: 0 <= j < i ==> s1[j] == s2[j]
  {
    if s1[i] < s2[i] {
      assert LexicographicLess(s1, s2);
      return -1;
    } else if s1[i] > s2[i] {
      assert LexicographicLess(s2, s1);
      return 1;
    }
    i := i + 1;
  }
  assert s1 == s2;
  return 0;
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
  
  if |t1| < |t2| {
    NormalizedComparison(t1, t2);
    res := -1;
  } else if |t1| > |t2| {
    NormalizedComparison(t1, t2);
    res := 1;
  } else {
    NormalizedComparison(t1, t2);
    res := LexicographicCompare(t1, t2);
    if res == -1 {
      assert LexicographicLess(t1, t2);
      assert Str2Int(t1) < Str2Int(t2);
    } else if res == 0 {
      assert t1 == t2;
      assert Str2Int(t1) == Str2Int(t2);
    } else {
      assert res == 1;
      assert LexicographicLess(t2, t1);
      assert Str2Int(t1) > Str2Int(t2);
    }
  }
}
// </vc-code>

