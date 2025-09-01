

// <vc-helpers>
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
  prefixes := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |prefixes| == i
    invariant forall j :: 0 <= j < i ==> prefixes[j] == s[..j+1]
  {
    prefixes := prefixes + [s[..i+1]];
    i := i + 1;
  }
}
// </vc-code>

