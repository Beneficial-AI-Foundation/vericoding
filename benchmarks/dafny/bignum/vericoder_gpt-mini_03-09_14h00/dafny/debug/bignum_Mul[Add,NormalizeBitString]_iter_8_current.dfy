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
  ghost var n1 := Str2Int(s1);
  ghost var n2 := Str2Int(s2);
  ghost var prod := n1 * n2;
  res := NatToBitString(prod);
}
// </vc-code>

