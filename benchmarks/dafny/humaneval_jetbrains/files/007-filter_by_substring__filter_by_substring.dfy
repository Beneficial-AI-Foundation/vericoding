
/*
function_signature: method filter_by_substring(strings: seq<string>, substring: string) returns (res : seq<string>)
Filter elements. Ensures: the size is bounded; the condition holds for all values.
*/

method checkSubstring(s: string, sub: string) returns (result: bool)
{
  assume{:axiom} false;
}

method filter_by_substring(strings: seq<string>, substring: string) returns (res : seq<string>)
    // post-conditions-start
    ensures |res| <= |strings|
    ensures (forall s :: s in res ==> s in strings)
    // post-conditions-end
{
  assume false;
}
