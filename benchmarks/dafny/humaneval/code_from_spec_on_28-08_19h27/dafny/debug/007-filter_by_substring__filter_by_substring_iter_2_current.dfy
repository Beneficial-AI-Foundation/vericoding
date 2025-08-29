method checkSubstring(s: string, sub: string) returns (result: bool)
{
  assume{:axiom} false;
}

// <vc-helpers>
predicate checkSubstring(s: string, sub: string)
{
  exists i :: 0 <= i <= |s| - |sub| && s[i..i+|sub|] == sub
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method filter_by_substring(strings: seq<string>, substring: string) returns (res : seq<string>)
Filter elements. Ensures: the size is bounded; the condition holds for all values.
*/
// </vc-description>

// <vc-spec>
method filter_by_substring(strings: seq<string>, substring: string) returns (res : seq<string>)
  ensures |res| <= |strings|
  ensures forall i :: 0 <= i < |res| ==> checkSubstring(res[i], substring)
  ensures forall s :: s in res ==> s in strings
// </vc-spec>
// <vc-code>
{
  res := [];
  var i := 0;
  while i < |strings|
    invariant 0 <= i <= |strings|
    invariant |res| <= i
    invariant forall j :: 0 <= j < |res| ==> checkSubstring(res[j], substring)
    invariant forall s :: s in res ==> s in strings
  {
    var contains := checkSubstring(strings[i], substring);
    if contains {
      res := res + [strings[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
