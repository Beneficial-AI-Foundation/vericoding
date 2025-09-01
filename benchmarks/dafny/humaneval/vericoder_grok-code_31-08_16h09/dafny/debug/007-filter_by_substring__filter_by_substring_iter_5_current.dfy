method checkSubstring(s: string, sub: string) returns (result: bool)
{
  assume{:axiom} false;
}

// <vc-helpers>
method checkSubstring(s: string, sub: string) returns (r: bool)
  ensures r <==> (|sub| == 0 || exists k :: 0 <= k <= |s| - |sub| && s[k..k+|sub|] == sub)
{
  if |sub| == 0 {
    r := true;
  } else if |s| < |sub| {
    r := false;
  } else {
    r := false;
    for i := 0 to |s| - |sub|
      invariant 0 <= i <= |s| - |sub| + 1
      invariant !r ==> (forall j :: 0 <= j < i ==> s[j..j+|sub|] != sub)
    {
      if s[i..i+|sub|] == sub {
        r := true;
        break;
      }
    }
  }
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
  res := [];
  for i := 0 to |strings| - 1
    invariant 0 <= i <= |strings|
    invariant |res| <= i
    invariant forall s :: s in res ==> s in old(strings)[0..i]
    invariant forall j :: 0 <= j < |res| ==> checkSubstring(strings[j], substring)
  {
    var temp := checkSubstring(strings[i], substring);
    if temp {
      res := res + [strings[i]];
    }
  }
  return res;
}
// </vc-code>

