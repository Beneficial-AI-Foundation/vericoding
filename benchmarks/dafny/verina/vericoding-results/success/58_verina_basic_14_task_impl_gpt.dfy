// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsZ(c: char) { c == 'z' || c == 'Z' }
// </vc-helpers>

// <vc-spec>
method ContainsZ(s: string) returns (result: bool)
    ensures
        result <==> exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z')
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var w := -1;
  result := false;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant result ==> 0 <= w && w < i && IsZ(s[w])
    invariant !result ==> w == -1
    invariant !result ==> (forall j :: 0 <= j < i ==> !IsZ(s[j]))
    decreases |s| - i
  {
    if IsZ(s[i]) {
      result := true;
      w := i;
    }
    i := i + 1;
  }
}
// </vc-code>
