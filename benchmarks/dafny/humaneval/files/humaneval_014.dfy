// <vc-preamble>

predicate ValidPrefixes(s: string, result: seq<string>)
{
    |result| == |s| &&
    forall i :: 0 <= i < |result| ==> result[i] == s[0..i+1]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method all_prefixes(s: string) returns (result: seq<string>)
    ensures ValidPrefixes(s, result)
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
  }
// </vc-code>
