

// <vc-helpers>
function isDigit(c: char): bool
  ensures isDigit(c) <==> (c in "0123456789")
{
  c in "0123456789"
}
// </vc-helpers>

// <vc-spec>
method allDigits(s: string) returns (result: bool)
  ensures  result <==> (forall i :: 0 <= i < |s| ==> s[i] in "0123456789")
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall j :: 0 <= j < i ==> isDigit(s[j])
  {
    if !isDigit(s[i]) {
      return false;
    }
    i := i + 1;
  }
  return true;
}
// </vc-code>

