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
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(s) == Str2Int(t)
{
  var i := 0;
  while i < |s| - 1 && s[i] == '0'
    invariant 0 <= i <= |s|
    invariant forall j | 0 <= j < i :: s[j] == '0'
    invariant Str2Int(s) == Str2Int(s[i..])
  {
    i := i + 1;
  }
  t := s[i..];
}

lemma CompareUnequalLemma(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires |s1| > 0
  requires |s1| > 1 ==> s1[0] != '0'
  requires |s2| > 0
  requires |s2| > 1 ==> s2[0] != '0'
  requires Str2Int(s1) != Str2Int(s2)
  ensures |s1| > |s2| ==> Str2Int(s1) > Str2Int(s2)
  ensures |s1| < |s2| ==> Str2Int(s1) < Str2Int(s2)
  ensures |s1| == |s2| ==> Str2Int(s1) < Str2Int(s2) <==> s1 < s2
{
  if |s1| > |s2| {
    var s2ext := s2 + "0" * (|s1| - |s2|);
    assert Str2Int(s2ext) == Str2Int(s2) * (1 << (|s1| - |s2|));
    assert Str2Int(s1) >= (1 << (|s1| - 1));
    assert Str2Int(s2) < (1 << |s2|);
    calc {
      Str2Int(s2) * (1 << (|s1| - |s2|));
      <= (1 << |s2| - 1) * (1 << (|s1| - |s2|));
      == (1 << |s1| - 1);
      <= (1 << |s1| - 1);
      < (1 << |s1| - 1) + 1;
      <= Str2Int(s1);
    }
  } else if |s1| < |s2| {
    assert Str2Int(s1) < Str2Int(s2) by {
      calc {
        Str2Int(s1);
        < (1 << |s1|);
        <= (1 << |s2| - 1);
        <= Str2Int(s2);
      }
    }
  } else {
    if |s1| == 0 {
      assert s1 == "" && s2 == "" && Str2Int(s1) == 0 && Str2Int(s2) == 0;
    } else {
      var i := 0;
      while i < |s1| && s1[i] == s2[i]
        invariant 0 <= i <= |s1|
        invariant forall j | 0 <= j < i :: s1[j] == s2[j]
      {
        i := i + 1;
      }
      if i < |s1| {
        if s1[i] != s2[i] {
          if s1[i] == '1' {
            assert Str2Int(s1) > Str2Int(s2);
          } else {
            assert Str2Int(s1) < Str2Int(s2);
          }
        }
      }
    }
  }
}

lemma NormalizeBitStringPreservesValue(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) == Str2Int(NormalizeBitString(s))
{
  var i := 0;
  while i < |s| - 1 && s[i] == '0'
    invariant 0 <= i <= |s|
    invariant forall j | 0 <= j < i :: s[j] == '0'
    invariant Str2Int(s) == Str2Int(s[i..])
  {
    i := i + 1;
  }
  assert Str2Int(s) == Str2Int(NormalizeBitString(s));
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
  var ns1 := NormalizeBitString(s1);
  var ns2 := NormalizeBitString(s2);
  NormalizeBitStringPreservesValue(s1);
  NormalizeBitStringPreservesValue(s2);
  
  if ns1 == ns2 {
    return 0;
  } else {
    if |ns1| > |ns2| {
      return 1;
    } else if |ns1| < |ns2| {
      return -1;
    } else {
      var i := 0;
      while i < |ns1| && ns1[i] == ns2[i]
        invariant 0 <= i <= |ns1|
        invariant forall j | 0 <= j < i :: ns1[j] == ns2[j]
      {
        i := i + 1;
      }
      if i < |ns1| {
        if ns1[i] == '1' {
          return 1;
        } else {
          return -1;
        }
      } else {
        return 0;
      }
    }
  }
}
// </vc-code>

