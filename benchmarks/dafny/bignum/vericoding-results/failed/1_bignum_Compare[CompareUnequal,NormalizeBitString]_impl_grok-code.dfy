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
ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then 0 else (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
predicate ValidBitString(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

lemma Str2IntAllZeros(s: string)
  requires ValidBitString(s)
  requires forall i | 0 <= i < |s| :: s[i] == '0'
  ensures Str2Int(s) == 0
{
  if |s| == 0 {
  } else {
    assert s[|s|-1] == '0';
    Str2IntAllZeros(s[0..|s|-1]);
  }
}

lemma Str2IntLength(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires |s1| < |s2|
  requires |s1| > 0
  requires |s2| > 0
  ensures Str2Int(s1) < Str2Int(s2)
{
  if |s1| == 0 {
  } else if |s2| == 0 {
  } else if s1[|s1|-1] == '1' {
    assert Str2Int(s2) >= 1;
  } else {
    assert s2[|s2|-1] == '0' || s2[|s2|-1] == '1';
    Str2IntLength(s1[0..|s1|-1], s2[0..|s2|-1]);
  }
}

method NormalizeBitString(s: string) returns (t: string)
  requires ValidBitString(s)
  ensures ValidBitString(t)
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures Str2Int(s) == Str2Int(t)
{
  if |s| == 0 {
    t := "0";
  } else {
    var pos := 0;
    while pos < |s| && s[pos] == '0'
      invariant 0 <= pos <= |s|
      invariant forall k | 0 <= k < pos :: s[k] == '0'
      decreases |s| - pos
    {
      pos := pos + 1;
    }
    if pos == |s| {
      t := "0";
      Str2IntAllZeros(s[0..pos]);
    } else {
      t := s[pos..];
      Str2IntAllZeros(s[0..pos]);
    }
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
  var n1 := NormalizeBitString(s1);
  var n2 := NormalizeBitString(s2);
  if |n1| < |n2| {
    Str2IntLength(n1, n2);
    return -1;
  } else if |n1| > |n2| {
    Str2IntLength(n2, n1);
    return 1;
  } else {
    if n1 < n2 {
      return -1;
    } else if n1 > n2 {
      return 1;
    } else {
      return 0;
    }
  }
}
// </vc-code>

