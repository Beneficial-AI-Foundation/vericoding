// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsDigit(c: char) { c in "0123456789" }
// </vc-helpers>

// <vc-spec>
method allDigits(s: string) returns (result: bool)
  ensures  result <==> (forall i :: 0 <= i < |s| ==> s[i] in "0123456789")
// </vc-spec>
// <vc-code>
{
  var i: nat := 0;
  while i < |s|
    invariant i <= |s|
    invariant forall k :: 0 <= k < i ==> s[k] in "0123456789"
  {
    if !IsDigit(s[i]) {
      result := false;
      return;
    }
    i := i + 1;
  }
  result := true;
}
// </vc-code>
