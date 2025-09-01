method checkSubstring(s: string, sub: string) returns (result: bool)
{
  assume{:axiom} false;
}

// <vc-helpers>
method checkSubstring(s: string, sub: string) returns (result: bool)
{
  result := sub in s;
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
  var res := [];
  for i := 0 to |strings| - 1
  {
    if checkSubstring(strings[i], substring) {
      res := res + [strings[i]];
    }
  }
  return res;
}
// </vc-code>

