

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method checkSubstring(s: string, sub: string) returns (result: bool)
// </vc-spec>
// <vc-code>
{
  if |sub| == 0 {
    result := true;
    return;
  }
  if |sub| > |s| {
    result := false;
    return;
  }
  var i := 0;
  while i <= |s| - |sub|
    invariant 0 <= i <= |s| - |sub| + 1
    invariant |sub| > 0
    decreases |s| - |sub| + 1 - i
  {
    var j := 0;
    var isMatch := true;
    while isMatch && j < |sub|
      invariant 0 <= j <= |sub|
      invariant 0 <= i
      invariant i <= |s| - |sub|
      invariant isMatch ==> (forall k:int :: 0 <= k < j ==> s[i + k] == sub[k])
      decreases (if isMatch then 1 else 0), |sub| - j
    {
      assert i + j < |s|;
      if s[i + j] == sub[j] {
        j := j + 1;
      } else {
        isMatch := false;
      }
    }
    if isMatch {
      assert j == |sub|;
      result := true;
      return;
    }
    i := i + 1;
  }
  result := false;
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