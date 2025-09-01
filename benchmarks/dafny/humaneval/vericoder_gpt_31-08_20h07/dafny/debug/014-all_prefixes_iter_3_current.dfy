

// <vc-helpers>
// no helpers needed
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
  var k := 0;
  prefixes := [];
  while k < |s|
    invariant 0 <= k <= |s|
    invariant |prefixes| == k
    invariant forall i :: 0 <= i < k ==> prefixes[i] == s[..i+1]
    decreases |s| - k
  {
    prefixes := prefixes + [s[..k+1]];
    k := k + 1;
  }
}
// </vc-code>

