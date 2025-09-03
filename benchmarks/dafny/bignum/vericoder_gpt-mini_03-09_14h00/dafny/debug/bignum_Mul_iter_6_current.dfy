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
lemma EvenDecomp(n: nat)
  ensures 2*(n/2) + n%2 == n
  decreases n
{
  if n == 0 { }
  else {
    EvenDecomp(n/2);
  }
}

lemma Str2Int_Push(s: string, i: int)
  requires ValidBitString(s)
  requires 0 <= i < |s|
  ensures Str2Int(s[0..i+1]) == 2*Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0)
{
  assert |s[0..i+1]| == i+1;
  assert Str2Int(s[0..i+1]) == 2 * Str2Int((s[0..i+1])[0..|s[0..i+1]|-1]) + (if (s[0..i+1])[|s[0..i+1]|-1] == '1' then 1 else 0);
  assert (s[0..i+1])[|s[0..i+1]|-1] == s[i];
  assert (s[0..i+1])[0..|s[0..i+1]|-1] == s[0..i];
  assert Str2Int(s[0..i+1]) == 2*Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0);
}

method Parse(s: string) returns (n: nat)
  requires ValidBitString(s)
  ensures n == Str2Int(s)
{
  var acc := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant acc == Str2Int(s[0..i])
    invariant forall k | 0 <= k < i :: s[k] == '0' || s[k] == '1'
  {
    var oldAcc := acc;
    var bit := if s[i] == '1' then 1 else 0;
    acc := 2 * oldAcc + bit;
    assert oldAcc == Str2Int(s[0..i]);
    Str2Int_Push(s, i);
    assert acc == Str2Int(s[0..i+1]);
    i := i + 1;
  }
  // i == |s| here
  assert i == |s|;
  assert acc == Str2Int(s[0..i]);
  assert acc == Str2Int(s);
  n := acc;
}

method BinOf(n: nat) returns (res: string)
  ensures ValidBitString(res)
  ensures Str2Int(res) == n
  decreases n
{
  if n == 0 {
    res := "";
    return;
  }
  var rest := BinOf(n / 2);
  var bit := n % 2;
  var bitStr := if bit == 1 then "1" else "0";
  res := rest + bitStr;
  assert Str2Int(res) == 2 * Str2Int(rest) + (if bitStr == "1" then 1 else 0);
  assert Str2Int(rest) == n / 2;
  if bit == 1 {
    assert bitStr == "1";
  } else {
    assert bitStr == "0";
  }
  assert (if bitStr == "1" then 1 else 0) == bit;
  EvenDecomp(n);
  assert Str2Int(res) == n;
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
  var i1 := 0;
  var acc1 := 0;
  while i1 < |s1|
    invariant 0 <= i1 <= |s1|
    invariant acc1 == Str2Int(s1[0..i1])
    invariant forall k | 0 <= k < i1 :: s1[k] == '0' || s1[k] == '1'
  {
    var oldAcc := acc1;
    var bit := if s1[i1] == '1' then 1 else 0;
    acc1 := 2 * oldAcc + bit;
    assert oldAcc == Str2Int(s1[0..i1]);
    Str2Int_Push(s1, i1);
    assert acc1 == Str2Int(s1[0..i1+1]);
    i1 := i1 + 1;
  }
  assert i1 == |s1|;
  assert acc1 == Str2Int(s1);
  var n1 := acc1;

  var i2 := 0;
  var acc2 := 0;
  while i2 < |s2|
    invariant 0 <= i2 <= |s2|
    invariant acc2 == Str2Int(s2[0..i2])
    invariant forall k | 0 <= k < i2 :: s2[k] == '0' || s2[k] == '1'
  {
    var oldAcc := acc2;
    var bit := if s2[i2] == '1' then 1 else 0;
    acc2 := 2 * oldAcc + bit;
    assert oldAcc == Str2Int(s2[0..i2]);
    Str2Int_Push(s2, i2);
    assert acc2 == Str2Int(s2[0..i2+1]);
    i2 := i2 + 1;
  }
  assert i2 == |s2|;
  assert acc2 == Str2Int(s2);
  var n2 := acc2;

  var p := n1 * n2;
  res := BinOf(p);
}
// </vc-code>

