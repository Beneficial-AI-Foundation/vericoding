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
  ensures ValidBitString(t)
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(s) == Str2Int(t)
{
  assume{:axiom} false;
}

// <vc-helpers>
method Str2IntPrefixStep(s: string, i: nat)
  requires 0 <= i < |s|
  requires ValidBitString(s)
  ensures Str2Int(s[0..i+1]) == 2 * Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0)
{
  var t := s[0..i+1];
  // prove ValidBitString(t) from ValidBitString(s)
  var k := 0;
  while k < |t|
    decreases |t| - k
  {
    assert t[k] == s[k];
    assert s[k] == '0' || s[k] == '1';
    assert t[k] == '0' || t[k] == '1';
    k := k + 1;
  }
  assert ValidBitString(t);

  // relate Str2Int(t) to its prefix and last character
  assert |t| == i + 1;
  assert t[0..|t|-1] == s[0..i];
  assert t[|t|-1] == s[i];
  assert Str2Int(t) == (if |t| == 0 then 0 else 2 * Str2Int(t[0..|t|-1]) + (if t[|t|-1] == '1' then 1 else 0));
  // since |t| = i+1 > 0, we can simplify
  assert Str2Int(t) == 2 * Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0);
}

method ValidPrefixIsValid(s: string, k: nat)
  requires ValidBitString(s)
  requires 0 <= k <= |s|
  ensures ValidBitString(s[0..k])
{
  var i := 0;
  var t := s[0..k];
  while i < |t|
    decreases |t| - i
  {
    assert t[i] == s[i];
    assert s[i] == '0' || s[i] == '1';
    assert t[i] == '0' || t[i] == '1';
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
// </vc-spec>
// <vc-code>
{
  var a: nat := 0;
  var i: nat := 0;
  while i < |s1|
    decreases |s1| - i
    invariant 0 <= i <= |s1|
    invariant ValidBitString(s1[0..i])
    invariant a == Str2Int(s1[0..i])
  {
    var bit := if s1[i] == '1' then 1 else 0;
    var newa := 2 * a + bit;
    // By lemma, Str2Int(s1[0..i+1]) == 2*Str2Int(s1[0..i]) + bit
    Str2IntPrefixStep(s1, i);
    // Now newa == Str2Int(s1[0..i+1])
    assert newa == Str2Int(s1[0..i+1]);
    a := newa;
    ValidPrefixIsValid(s1, i + 1);
    i := i + 1;
  }
  // at loop exit, i == |s1| and therefore a == Str2Int(s1)
  assert a == Str2Int(s1);

  var b: nat := 0;
  i := 0;
  while i < |s2|
    decreases |s2| - i
    invariant 0 <= i <= |s2|
    invariant ValidBitString(s2[0..i])
    invariant b == Str2Int(s2[0..i])
  {
    var bit := if s2[i] == '1' then 1 else 0;
    var newb := 2 * b + bit;
    Str2IntPrefixStep(s2, i);
    assert newb == Str2Int(s2[0..i+1]);
    b := newb;
    ValidPrefixIsValid(s2, i + 1);
    i := i + 1;
  }
  // at loop exit, i == |s2| and therefore b == Str2Int(s2)
  assert b == Str2Int(s2);

  var p: nat := a * b;
  // ensure the IntToBitString postconditions will yield the required result
  res := IntToBitString(p);
  // IntToBitString ensures Str2Int(res) == p and ValidBitString(res)
  assert Str2Int(res) == p;
  assert p == Str2Int(s1) * Str2Int(s2);
}
// </vc-code>

