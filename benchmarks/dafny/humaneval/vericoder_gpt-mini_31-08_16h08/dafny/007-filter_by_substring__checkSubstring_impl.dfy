

// <vc-helpers>
// No additional helpers required.
// </vc-helpers>

// <vc-spec>
method checkSubstring(s: string, sub: string) returns (result: bool)
// </vc-spec>
// <vc-code>
{
  var n := |s|;
  var m := |sub|;
  if m == 0 {
    result := true;
    return;
  }
  if m > n {
    result := false;
    return;
  }
  var i := 0;
  result := false;
  while i <= n - m
    decreases n - m - i
  {
    var j := 0;
    var isMatch := true;
    while j < m
      decreases m - j
    {
      if s[i + j] != sub[j] {
        isMatch := false;
        j := m;
      } else {
        j := j + 1;
      }
    }
    if isMatch && j == m {
      result := true;
      return;
    }
    i := i + 1;
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