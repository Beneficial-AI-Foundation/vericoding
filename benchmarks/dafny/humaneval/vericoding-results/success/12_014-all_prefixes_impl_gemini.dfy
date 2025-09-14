// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method all_prefixes(s: string) returns (prefixes: seq<string>)

    ensures |prefixes| == |s|
    ensures forall i :: 0 <= i < |prefixes| ==> s[..i+1] == prefixes[i]
// </vc-spec>
// <vc-code>
{
  prefixes := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |prefixes| == i
    invariant forall j :: 0 <= j < i ==> s[..j+1] == prefixes[j]
  {
    var p := s[..i+1];
    prefixes := prefixes + [p];
    i := i + 1;
  }
}
// </vc-code>
