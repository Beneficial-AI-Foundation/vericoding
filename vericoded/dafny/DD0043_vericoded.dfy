

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method allDigits(s: string) returns (result: bool)
  ensures  result <==> (forall i :: 0 <= i < |s| ==> s[i] in "0123456789")
// </vc-spec>
// <vc-code>
{
  result := true;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant result <==> (forall j :: 0 <= j < i ==> s[j] in "0123456789")
  {
    if !(s[i] in "0123456789") {
      result := false;
    }
    i := i + 1;
  }
}
// </vc-code>

