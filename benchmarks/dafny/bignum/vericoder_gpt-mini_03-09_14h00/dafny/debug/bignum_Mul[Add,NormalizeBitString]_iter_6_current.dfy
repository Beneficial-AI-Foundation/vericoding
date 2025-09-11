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

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  assume{:axiom} false;
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
function NatToBitString(n: nat): string
  decreases n
  ensures ValidBitString(NatToBitString(n))
  ensures Str2Int(NatToBitString(n)) == n
{
  if n == 0 then "0"
  else NatToBitString(n / 2) + (if n % 2 == 1 then "1" else "0")
}

lemma Str2Int_PrefixExtend(s: string, i: int)
  requires ValidBitString(s)
  requires 0 <= i < |s|
  ensures Str2Int(s[0..i+1]) == 2 * Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0)
{
  var t := s[0..i+1];
  assert |t| == i + 1;
  assert t[0..|t|-1] == s[0..i];
  assert t[|t|-1] == s[i];
  if |t| != 0 {
    assert Str2Int(t) == 2 * Str2Int(t[0..|t|-1]) + (if t[|t|-1] == '1' then 1 else 0);
    assert Str2Int(t) == 2 * Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0);
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
  res := "0";
  ghost var acc: nat := 0;
  var i := 0;
  var n2 := |s2|;
  while i < n2
    invariant 0 <= i <= n2
    invariant ValidBitString(res)
    invariant Str2Int(res) == Str2Int(s1) * acc
    invariant acc == Str2Int(s2[0..i])
    decreases n2 - i
  {
    var doubled := Add(res, res);
    var c := s2[i];
    ghost var oldAcc := acc;
    if c == '1' {
      res := Add(doubled, s1);
      acc := oldAcc * 2 + 1;
    } else {
      res := doubled;
      acc := oldAcc * 2;
    }
    Str2Int_PrefixExtend(s2, i);
    assert oldAcc == Str2Int(s2[0..i]);
    if c == '1' {
      assert acc == 2 * oldAcc + 1;
      assert acc == Str2Int(s2[0..i+1]);
    } else {
      assert acc == 2 * oldAcc;
      assert acc == Str2Int(s2[0..i+1]);
    }
    i := i + 1;
  }
}
// </vc-code>

