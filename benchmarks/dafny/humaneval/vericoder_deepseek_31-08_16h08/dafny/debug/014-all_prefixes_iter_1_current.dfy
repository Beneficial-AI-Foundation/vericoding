

// <vc-helpers>
lemma Lemma_AppendSubsequence(s: string, i: int)
  requires 0 <= i <= |s|
  ensures s[..i+1] == s[..i] + [s[i]]
{
}
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
    prefixes := [s[..1]] + p;
  }
}
// </vc-code>

