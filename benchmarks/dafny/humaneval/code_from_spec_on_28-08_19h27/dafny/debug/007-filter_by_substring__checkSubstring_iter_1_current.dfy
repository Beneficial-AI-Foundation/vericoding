// <vc-helpers>
// </vc-helpers>

// <vc-description>
/*
function_signature: method checkSubstring(s: string, sub: string) returns (result: bool)
Check condition.
*/
// </vc-description>

// <vc-spec>
method checkSubstring(s: string, sub: string) returns (result: bool)
    ensures result <==> (sub in s)
// </vc-spec>
// <vc-code>
{
    result := sub in s;
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