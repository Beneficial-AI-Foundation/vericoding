

// <vc-helpers>
predicate isSubstring(s: string, sub: string) {
    var n := |s|;
    var m := |sub|;
    if m == 0 then true else
    if n < m then false else
    exists start {:trigger s[start..start+m]} :: 0 <= start <= n - m && s[start..start+m] == sub
}
// </vc-helpers>

// <vc-spec>
method checkSubstring(s: string, sub: string) returns (result: bool)
// </vc-spec>
// <vc-code>
{
    return isSubstring(s, sub);
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