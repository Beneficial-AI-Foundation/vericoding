ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
predicate ValidBitString(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

// <vc-helpers>
function {:inline} AllZeros(s: string): bool
  requires ValidBitString(s)
{
  forall i | 0 <= i < |s| :: s[i] == '0'
}

lemma RemoveLeadingZero(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  requires s[0] == '0'
  ensures Str2Int(s) == Str2Int(s[1..])
  decreases |s|
{
  if |s| == 1 {
    assert s == "0";
    assert s[1..] == "";
    assert Str2Int(s) == 0;
    assert Str2Int(s[1..]) == 0;
  } else {
    calc {
      Str2Int(s);
      2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1]=='1' then 1 else 0);
      { 
        RemoveLeadingZero(s[0..|s|-1]);
        assert Str2Int(s[0..|s|-1]) == Str2Int(s[0..|s|-1][1..]);
      }
      2 * Str2Int(s[1..|s|-1]) + (if s[|s|-1]=='1' then 1 else 0);
      {
        assert s[1..] == s[1..|s|-1] + [s[|s|-1]];
      }
      Str2Int(s[1..]);
    }
  }
}

lemma StripLeadingZerosPreservesValue(s: string, n: nat)
  requires ValidBitString(s)
  requires n <= |s|
  requires AllZeros(s[0..n])
  ensures Str2Int(s) == Str2Int(s[n..])
  decreases n
{
  if n == 0 {
  } else {
    RemoveLeadingZero(s);
    StripLeadingZerosPreservesValue(s[1..], n-1);
  }
}

lemma AllZerosImpliesZero(s: string)
  requires ValidBitString(s)
  requires AllZeros(s)
  ensures Str2Int(s) == 0
  decreases |s|
{
  if |s| == 0 {
  } else {
    calc {
      Str2Int(s);
      2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1]=='1' then 1 else 0);
      { 
        AllZerosImpliesZero(s[0..|s|-1]);
        assert Str2Int(s[0..|s|-1]) == 0;
      }
      2 * 0 + 0;
      0;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method NormalizeBitString(s: string) returns(t: string)
  ensures ValidBitString(t)
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(s) == Str2Int(t)
// </vc-spec>
// <vc-code>
{
  if !ValidBitString(s) {
    return "0";
  }
  var n := 0;
  while n < |s| && s[n] == '0'
    invariant 0 <= n <= |s|
    invariant forall i | 0 <= i < n :: s[i] == '0'
    decreases |s| - n
  {
    n := n + 1;
  }
  if n == |s| {
    assert AllZeros(s);
    AllZerosImpliesZero(s);
    return "0";
  } else {
    assert n < |s|;
    assert AllZeros(s[0..n]);
    var t := s[n..];
    StripLeadingZerosPreservesValue(s, n);
    return t;
  }
}
// </vc-code>

