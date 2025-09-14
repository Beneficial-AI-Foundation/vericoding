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
function BVal(s: string): int
  decreases s
{
  if |s| == 0 then 0 else 2 * BVal(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
}

lemma ValidBitStringPrefix(s: string, k: int)
  requires ValidBitString(s)
  requires 0 <= k <= |s|
  ensures ValidBitString(s[0..k])
{
  assert |s[0..k]| == k;
  forall i | 0 <= i < |s[0..k]|
    ensures (s[0..k])[i] == '0' || (s[0..k])[i] == '1'
  {
    assert |s[0..k]| == k;
    assert 0 <= i < |s|;
    assert s[i] == '0' || s[i] == '1';
    assert (s[0..k])[i] == s[i];
    assert (s[0..k])[i] == '0' || (s[0..k])[i] == '1';
  }
}

lemma BValEq(s: string)
  requires ValidBitString(s)
  ensures BVal(s) == Str2Int(s)
  decreases s
{
  if |s| == 0 {
  } else {
    ValidBitStringPrefix(s, |s|-1);
    BValEq(s[0..|s|-1]);
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
  var v1 := BVal(s1);
  var v2 := BVal(s2);
  BValEq(s1);
  BValEq(s2);
  assert v1 == Str2Int(s1);
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

