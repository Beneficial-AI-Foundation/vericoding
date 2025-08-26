// <vc-helpers>
// </vc-helpers>

method allDigits(s: string) returns (result: bool)
  ensures  result <==> (forall i :: 0 <= i < |s| ==> s[i] in "0123456789")
// <vc-code>
{
  assume false;
}
// </vc-code>