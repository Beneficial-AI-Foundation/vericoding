

// <vc-helpers>
// Helper code for substring checking can be implemented directly in the method if needed, no additional helpers required.
// </vc-helpers>

// <vc-spec>
method checkSubstring(s: string, sub: string) returns (result: bool)
// </vc-spec>
// <vc-code>
{
  if |sub| == 0 {
    result := true;
  } else {
    var i := 0;
    while i <= |s| - |sub|
      invariant 0 <= i <= |s| - |sub| + 1
      invariant (forall j :: 0 <= j < i ==> s[j..j+|sub|] != sub)
    {
      if s[i..i+|sub|] == sub {
        result := true;
        return;
      }
      i := i + 1;
    }
    result := false;
  }
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