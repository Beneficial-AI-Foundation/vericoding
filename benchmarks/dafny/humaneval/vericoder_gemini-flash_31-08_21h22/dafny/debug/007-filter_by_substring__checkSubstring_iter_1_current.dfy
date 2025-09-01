

// <vc-helpers>
predicate {:opaque} IsSubstring(s: string, sub: string)
{
    exists i: int :: 0 <= i && i + |sub| <= |s| && s[i .. i + |sub|] == sub
}
// </vc-helpers>

// <vc-spec>
method checkSubstring(s: string, sub: string) returns (result: bool)
// </vc-spec>
// <vc-code>
{
  result := IsSubstring(s, sub);
}
// </vc-code>

method filter_by_substring(strings: seq<string>, substring: string) returns (res : seq<string>)
    // post-conditions-start
    ensures |res| <= |strings|
    ensures (forall s :: s in res ==> s in strings)
    // post-conditions-end
{
  assume{:axiom} false;
}