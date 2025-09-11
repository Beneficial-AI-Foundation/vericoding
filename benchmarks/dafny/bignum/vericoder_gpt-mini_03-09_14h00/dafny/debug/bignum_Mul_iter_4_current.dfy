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
  // |s[0..i+1]| == i+1 > 0, so by the definition of Str2Int on a non-empty string:
  assert |s[0..i+1]| == i+1;
  assert Str2Int(s[0..i+1]) == 2 * Str2Int((s[0..i+1])[0..|s[0..i+1]|-1]) + (if (s[0..i+1])[|s[0..i+1]|-1] == '1' then 1 else 0);
  // (s[0..i+1])[|s[0..i+1]|-1] is s[i], and (s[0..i+1])[0..|s[0..i+1]|-1] is s[0..i]
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
    // oldAcc == Str2Int(s[0..i]) by the loop invariant, and Str2Int_Push gives the step relation
    assert oldAcc == Str2Int(s[0..i]);
    Str2Int_Push(s, i);
    assert acc == Str2Int(s[0..i+1]);
    i := i + 1;
  }
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
  var bitStr := if n % 2 == 1 then "1" else "0";
  res := rest + bitStr;
  // res has last character bitStr, so Str2Int(res) = 2*Str2Int(rest) + bitVal
  // and by induction Str2Int(rest) == n/2, and by EvenDecomp 2*(n/2) + n%2 == n
  assert Str2Int(res) == 2 * Str2Int(rest) + (if bitStr == "1" then 1 else 0);
  assert Str2Int(rest) == n / 2;
  assert (if bitStr == "1" then 1 else 0) == n % 2;
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
  var n1 := Parse(s1);
  var n2 := Parse(s2);
  var p := n1 * n2;
  res := BinOf(p);
}
// </vc-code>

