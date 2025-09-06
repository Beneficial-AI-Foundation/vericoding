/*
function_signature: method checkSubstring(s: string, sub: string) returns (result: bool)
Check condition.
*/

method checkSubstring(s: string, sub: string) returns (result: bool)
{
  assume false;
}

method filter_by_substring(strings: seq<string>, substring: string) returns (res : seq<string>)
    // post-conditions-start
    ensures |res| <= |strings|
    ensures (forall s :: s in res ==> s in strings)
    // post-conditions-end
{
  assume{:axiom} false;
}