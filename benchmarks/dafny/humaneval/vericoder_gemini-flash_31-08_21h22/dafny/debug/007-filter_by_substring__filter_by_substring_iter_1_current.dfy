method checkSubstring(s: string, sub: string) returns (result: bool)
{
  assume{:axiom} false;
}

// <vc-helpers>
function method checkSubstring(s: string, sub: string): bool
{
  s.Contains(sub)
}
// </vc-helpers>

// <vc-spec>
method filter_by_substring(strings: seq<string>, substring: string) returns (res : seq<string>)
    // post-conditions-start
    ensures |res| <= |strings|
    ensures (forall s :: s in res ==> s in strings)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var result: seq<string> := [];
  for s in strings {
    if checkSubstring(s, substring) {
      result := result + [s];
    }
  }
  return result;
}
// </vc-code>

