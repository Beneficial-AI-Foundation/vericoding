method checkSubstring(s: string, sub: string) returns (result: bool)
{
  assume{:axiom} false;
}

// <vc-helpers>

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
  res := [];
  for i := 0 to |strings|
    invariant 0 <= i <= |strings|
    invariant |res| <= i
    invariant forall s :: s in res ==> s in strings[..i]
  {
    var contains := checkSubstring(strings[i], substring);
    if contains {
      res := res + [strings[i]];
    }
  }
}
// </vc-code>

