

// <vc-helpers>
predicate IsSubstring(s: string, sub: string)
{
    exists i: int :: 0 <= i && i + |sub| <= |s| && s[i .. i + |sub|] == sub
    by (
        if |sub| == 0 then
            // Any string contains an empty sub-string at index 0.
            true
        else if |s| < |sub| then
            // A string shorter than sub cannot contain it as a sub-string.
            false
        else
            // This is the normal case, where the built-in resolver for 'exists' should work.
            true
    )
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