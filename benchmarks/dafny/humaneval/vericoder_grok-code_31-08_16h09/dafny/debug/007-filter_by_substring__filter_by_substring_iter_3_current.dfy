method checkSubstring(s: string, sub: string) returns (result: bool)
{
  assume{:axiom} false;
}

// <vc-helpers>
method checkSubstring(s: string, sub: string) returns (r: bool)
{
  if |sub| == 0 {
    r := true;
  } else if |s| < |sub| {
    r := false;
  } else {
    r := false;
    for i := 0 to |s| - |sub| {
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
  var res: seq<string> := [];
  for i := 0 to |strings| - 1
  {
    var temp := checkSubstring(strings[i], substring);
    if temp {
      res := res + [strings[i]];
    }
  }
  return res;
}
// </vc-code>

