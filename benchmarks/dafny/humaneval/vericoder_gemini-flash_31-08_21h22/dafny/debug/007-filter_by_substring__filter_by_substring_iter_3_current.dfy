method checkSubstring(s: string, sub: string) returns (result: bool)
{
  assume{:axiom} false;
}

// <vc-helpers>
function checkSubstring(s: string, sub: string): bool
{
  sub in s // Use the 'in' operator for substring check
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
  var result: seq<string> := [];
  for i := 0 to |strings| - 1
    invariant 0 <= i <= |strings|
    invariant (forall j :: 0 <= j < i ==> (checkSubstring(strings[j], substring) <==> strings[j] in result))
    // We add an invariant to ensure that `result` only contains strings from `strings`.
    invariant (forall s :: s in result ==> s in strings)
  {
    var s := strings[i];
    if checkSubstring(s, substring)
    {
      result := result + [s];
    }
  }
  return result;
}
// </vc-code>

