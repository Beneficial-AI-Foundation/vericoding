method checkSubstring(s: string, sub: string) returns (result: bool)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma lemma_substring_in_string(s: string, sub: string)
  ensures sub in s ==> |sub| <= |s|
{
  if sub in s {
    assert |sub| <= |s|;
  }
}

lemma lemma_substring_not_in_string(s: string, sub: string)
  ensures (|sub| > |s|) ==> sub !in s
{
  if |sub| > |s| {
    assert sub !in s;
  }
}

lemma lemma_no_substring_empty(s: string)
  ensures "" in s
{
  assert "" in s;
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
  var i := 0;
  while i < |strings|
    invariant |res| <= i
    invariant (forall s :: s in res ==> s in strings)
  {
    if |substring| <= |strings[i]| && substring == strings[i][0..|substring|] {
      res := res + [strings[i]];
    }
    i := i + 1;
  }
}
// </vc-code>

