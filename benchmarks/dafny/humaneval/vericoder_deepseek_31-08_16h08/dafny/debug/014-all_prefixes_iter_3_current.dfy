

// <vc-helpers>
lemma Lemma_AppendSubsequence(s: string, i: int)
  requires 0 <= i < |s|
  ensures s[..i+1] == s[..i] + [s[i]]
{
}

lemma Lemma_AllPrefixesEmpty(s: string)
  ensures |s| == 0 ==> all_prefixes(s) == []
{
}

function method all_prefixes(s: string): seq<string>
  ensures |all_prefixes(s)| == |s|
  ensures forall i :: 0 <= i < |all_prefixes(s)| ==> s[..i+1] == all_prefixes(s)[i]
{
  if |s| == 0 then []
  else [s[..1]] + all_prefixes(s[1..])
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method all_prefixes(s: string) returns (prefixes: seq<string>)
    // post-conditions-start
    ensures |prefixes| == |s|
    ensures forall i :: 0 <= i < |prefixes| ==> s[..i+1] == prefixes[i]
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if |s| == 0 {
    prefixes := [];
  } else {
    var p := all_prefixes(s[1..]);
    assert |p| == |s| - 1;
    var first_prefix := s[..1];
    prefixes := [first_prefix] + p;
    
    // Verify the first element
    assert prefixes[0] == s[..1];
    
    // Verify remaining elements using induction hypothesis
    var i := 1;
    while i < |prefixes|
      invariant 1 <= i <= |prefixes|
      invariant forall j :: 0 < j < i ==> prefixes[j] == s[..j+1]
    {
      assert p[i-1] == s[1..][..i];
      assert prefixes[i] == p[i-1];
      assert s[..i+1] == s[..1] + s[1..][..i];
      i := i + 1;
    }
  }
}
// </vc-code>

