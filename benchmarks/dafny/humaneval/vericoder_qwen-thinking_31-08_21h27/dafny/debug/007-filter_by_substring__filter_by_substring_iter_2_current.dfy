method checkSubstring(s: string, sub: string) returns (result: bool)
{
  assume{:axiom} false;
}

// <vc-helpers>
method checkSubstring(s: string, sub: string) returns (result: bool)
    ensures result <==> s.Contains(sub)
{
    result := s.Contains(sub);
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
{ res := [s | s in strings; checkSubstring(s, substring)]; }
// </vc-code>

