

// <vc-helpers>
predicate isSubstring(s: string, sub: string)
{
  if |sub| == 0 then true
  else if |s| < |sub| then false
  else if s[0..|sub|] == sub then true
  else isSubstring(s[1..], sub)
}

lemma isSubstringLemma(s: string, sub: string)
  ensures isSubstring(s, sub) <==> (exists i: nat | i <= |s| - |sub| :: s[i..i+|sub|] == sub)
{
  // Helper lemma for isSubstring predicate
}
// </vc-helpers>

// <vc-spec>
method checkSubstring(s: string, sub: string) returns (result: bool)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  res := [];
  while i < |strings|
    invariant i <= |strings|
    invariant |res| <= i
    invariant forall s :: s in res ==> s in strings[0..i]
  {
    if isSubstring(strings[i], substring) {
      res := res + [strings[i]];
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