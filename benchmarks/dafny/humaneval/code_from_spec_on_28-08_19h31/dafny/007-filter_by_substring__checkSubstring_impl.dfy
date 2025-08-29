// <vc-helpers>
function containsSubstring(s: string, sub: string): bool
{
  if |sub| == 0 then true
  else if |s| < |sub| then false
  else if s[..|sub|] == sub then true
  else containsSubstring(s[1..], sub)
}

lemma SubstringCorrect(s: string, sub: string)
  ensures containsSubstring(s, sub) ==> exists i :: 0 <= i <= |s| - |sub| && s[i..i+|sub|] == sub
{
  if |sub| == 0 {
    assert s[0..0] == "";
  } else if |s| < |sub| {
    assert !containsSubstring(s, sub);
  } else if s[..|sub|] == sub {
    assert s[0..|sub|] == sub;
  } else {
    if containsSubstring(s[1..], sub) {
      var i :| 0 <= i <= |s[1..]| - |sub| && s[1..][i..i+|sub|] == sub;
      assert s[1+i..1+i+|sub|] == sub;
    }
  }
}

lemma NoSubstringImpliesNone(s: string, sub: string)
  requires !containsSubstring(s, sub)
  ensures forall k :: 0 <= k <= |s| - |sub| ==> s[k..k+|sub|] != sub
{
  if |sub| == 0 {
    assert false;
  } else if |s| < |sub| {
  } else {
    if s[..|sub|] != sub {
      if !containsSubstring(s[1..], sub) {
        NoSubstringImpliesNone(s[1..], sub);
        assert forall k :: 0 <= k <= |s[1..]| - |sub| ==> s[1..][k..k+|sub|] != sub;
        assert forall k :: 1 <= k <= |s| - |sub| ==> s[k..k+|sub|] != sub;
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
method checkSubstring(s: string, sub: string) returns (result: bool)
// </vc-spec>
// <vc-code>
method CheckSubstring(s: string, sub: string) returns (result: bool)
  ensures result == containsSubstring(s, sub)
{
  result := false;
  if |sub| == 0 {
    result := true;
    return;
  }
  if |s| < |sub| {
    result := false;
    return;
  }
  
  var i := 0;
  while i <= |s| - |sub|
    invariant 0 <= i <= |s| - |sub| + 1
    invariant !result ==> forall k :: 0 <= k < i && k <= |s| - |sub| ==> s[k..k+|sub|] != sub
    invariant result ==> exists k :: 0 <= k < i && k <= |s| - |sub| && s[k..k+|sub|] == sub
    decreases |s| - |sub| - i
  {
    if s[i..i+|sub|] == sub {
      result := true;
      return;
    }
    i := i + 1;
  }
  assert !result;
  assert forall k :: 0 <= k <= |s| - |sub| ==> s[k..k+|sub|] != sub;
  if !containsSubstring(s, sub) {
    NoSubstringImpliesNone(s, sub);
  }
  assert !containsSubstring(s, sub);
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