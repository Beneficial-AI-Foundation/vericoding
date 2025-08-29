method checkSubstring(s: string, sub: string) returns (result: bool)
{
  assume{:axiom} false;
}

// <vc-helpers>
predicate checkSubstring(s: string, sub: string)
{
  |sub| <= |s| && exists i :: 0 <= i <= |s| - |sub| && s[i..i+|sub|] == sub
}

method checkSubstringMethod(s: string, sub: string) returns (result: bool)
  ensures result <==> checkSubstring(s, sub)
{
  if |sub| > |s| {
    return false;
  }
  
  var i := 0;
  while i <= |s| - |sub|
    invariant 0 <= i <= |s| - |sub| + 1
    invariant forall j :: 0 <= j < i ==> s[j..j+|sub|] != sub
  {
    if s[i..i+|sub|] == sub {
      return true;
    }
    i := i + 1;
  }
  return false;
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
    var contains := checkSubstringMethod(strings[i], substring);
    if contains {
      res := res + [strings[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
