

// <vc-helpers>

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
  var p: seq<string> := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |p| == i
    invariant forall j :: 0 <= j < i ==> s[..j+1] == p[j]
    decreases |s| - i
  {
    p := p + [s[..i+1]];
    i := i + 1;
  }
  prefixes := p;
}
// </vc-code>

