

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method allDigits(s: string) returns (result: bool)
  ensures  result <==> (forall i :: 0 <= i < |s| ==> s[i] in "0123456789")
// </vc-spec>
// <vc-code>
{
  var i: int := 0;
  var allDigits: bool := true;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant allDigits <==> forall k :: 0 <= k < i ==> '0' <= s[k] <= '9'
  {
    if s[i] < '0' || s[i] > '9' {
      allDigits := false;
    }
    i := i + 1;
  }
  result := allDigits;
}
// </vc-code>

