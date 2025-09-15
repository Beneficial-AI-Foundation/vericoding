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
  return seq(|s|, i requires 0 <= i < |s| => s[..i+1]);
}
// </vc-code>
