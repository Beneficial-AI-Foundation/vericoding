// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ContainsZ(s: string) returns (result: bool)
    ensures
        result <==> exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z')
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall j :: 0 <= j < i ==> s[j] != 'z' && s[j] != 'Z'
  {
    if s[i] == 'z' || s[i] == 'Z' {
      return true;
    }
    i := i + 1;
  }
  return false;
}
// </vc-code>
