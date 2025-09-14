

// <vc-helpers>
method allDigitsFrom(s: string, i: int) returns (res: bool)
  requires 0 <= i <= |s|
  ensures  res <==> (forall j :: i <= j < |s| ==> s[j] in "0123456789")
  decreases |s| - i
{
  if i == |s| {
    res := true;
  } else {
    if s[i] in "0123456789" {
      res := allDigitsFrom(s, i + 1);
    } else {
      res := false;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method allDigits(s: string) returns (result: bool)
  ensures  result <==> (forall i :: 0 <= i < |s| ==> s[i] in "0123456789")
// </vc-spec>
// <vc-code>
{
  result := allDigitsFrom(s, 0);
}
// </vc-code>

