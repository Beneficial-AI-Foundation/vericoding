

// <vc-helpers>
// No changes needed in helpers for this fix
// </vc-helpers>

// <vc-spec>
method checkSubstring(s: string, sub: string) returns (result: bool)
// </vc-spec>
// <vc-code>
{
  if |sub| == 0 {
    result := true;
  } else if |sub| > |s| {
    result := false;
  } else {
    var i := 0;
    while i <= |s| - |sub|
      invariant 0 <= i <= |s| - |sub| + 1
      invariant (forall k :: 0 <= k < i ==> s[k..k+|sub|] != sub)
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