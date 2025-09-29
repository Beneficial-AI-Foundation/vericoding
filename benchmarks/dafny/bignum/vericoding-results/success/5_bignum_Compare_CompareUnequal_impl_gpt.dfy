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
lemma ValidBitString_Sub(s: string, lo: nat, hi: nat)
  requires 0 <= lo <= hi <= |s|
  requires ValidBitString(s)
  ensures ValidBitString(s[lo..hi])
{
  forall j | 0 <= j < |s[lo..hi]|
    ensures (s[lo..hi])[j] == '0' || (s[lo..hi])[j] == '1'
  {
    var k := lo + j;
    assert 0 <= k < |s|;
    assert (s[lo..hi])[j] == s[k];
    assert s[k] == '0' || s[k] == '1';
  }
}

lemma Str2Int_Step(s: string, i: nat)
  requires ValidBitString(s)
  requires i < |s|
  ensures Str2Int(s[0..i+1]) == 2 * Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0)
{
  ValidBitString_Sub(s, 0, i);
  ValidBitString_Sub(s, 0, i + 1);

  assert |s[0..i+1]| == i + 1;
  assert |s[0..i+1]| > 0;
  assert (s[0..i+1])[0..|s[0..i+1]| - 1] == s[0..i];
  assert (s[0..i+1])[|s[0..i+1]| - 1] == s[i];

  assert Str2Int(s[0..i+1]) ==
           2 * Str2Int((s[0..i+1])[0..|s[0..i+1]| - 1]) +
           (if (s[0..i+1])[|s[0..i+1]| - 1] == '1' then 1 else 0);
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
  var v1: int := 0;
  var i1: nat := 0;
  ValidBitString_Sub(s1, 0, 0);
  while i1 < |s1|
    invariant i1 <= |s1|
    invariant ValidBitString(s1)
    invariant ValidBitString(s1[0..i1])
    invariant v1 == Str2Int(s1[0..i1])
    decreases |s1| - i1
  {
    Str2Int_Step(s1, i1);
    v1 := 2 * v1 + (if s1[i1] == '1' then 1 else 0);
    i1 := i1 + 1;
    ValidBitString_Sub(s1, 0, i1);
  }
  assert s1[0..|s1|] == s1;
  assert v1 == Str2Int(s1);

  var v2: int := 0;
  var i2: nat := 0;
  ValidBitString_Sub(s2, 0, 0);
  while i2 < |s2|
    invariant i2 <= |s2|
    invariant ValidBitString(s2)
    invariant ValidBitString(s2[0..i2])
    invariant v2 == Str2Int(s2[0..i2])
    decreases |s2| - i2
  {
    Str2Int_Step(s2, i2);
    v2 := 2 * v2 + (if s2[i2] == '1' then 1 else 0);
    i2 := i2 + 1;
    ValidBitString_Sub(s2, 0, i2);
  }
  assert s2[0..|s2|] == s2;
  assert v2 == Str2Int(s2);

  if v1 < v2 {
    res := -1;
  } else if v1 == v2 {
    res := 0;
  } else {
    res := 1;
  }
}
// </vc-code>

