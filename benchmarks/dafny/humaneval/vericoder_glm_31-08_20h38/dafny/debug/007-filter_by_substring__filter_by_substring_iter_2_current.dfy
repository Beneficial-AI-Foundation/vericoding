method checkSubstring(s: string, sub: string) returns (result: bool)
{
  assume{:axiom} false;
}

// <vc-helpers>
predicate method contains(s: string, sub: string) {
    |s| >= |sub| && exists i :: 0 <= i <= |s| - |sub| && s[i..i+|sub|] == sub
}

lemma substring_containment(s: string, sub: string, i: int)
    requires 0 <= i <= |s| - |sub|
    requires s[i..i+|sub|] == sub
    ensures contains(s, sub)
{
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
    var filtered := [];
    for i := 0 to |strings|
    {
        if contains(strings[i], substring) {
            filtered := filtered + [strings[i]];
        }
    }
    res := filtered;
}
// </vc-code>

