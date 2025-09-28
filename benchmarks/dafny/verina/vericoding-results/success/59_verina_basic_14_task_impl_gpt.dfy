// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsZ(c: char)
{
  c == 'z' || c == 'Z'
}

predicate HasZ(s: string)
{
  exists i :: 0 <= i < |s| && IsZ(s[i])
}
// </vc-helpers>

// <vc-spec>
method ContainsZ(s: string) returns (result: bool)
    ensures
        result <==> exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z')
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var found := false;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant found ==> exists j :: 0 <= j < i && (s[j] == 'z' || s[j] == 'Z')
    invariant !found ==> forall j :: 0 <= j < i ==> (s[j] != 'z' && s[j] != 'Z')
    decreases |s| - i
  {
    if s[i] == 'z' || s[i] == 'Z' {
      found := true;
    }
    i := i + 1;
  }
  result := found;
}
// </vc-code>
