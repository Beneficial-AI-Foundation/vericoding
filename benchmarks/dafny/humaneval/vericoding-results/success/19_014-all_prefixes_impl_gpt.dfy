// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): replaced comprehension with recursive construction to fix parse error and ensure properties */
function Prefixes(s: string): seq<string>
  ensures |Prefixes(s)| == |s|
  ensures forall i :: 0 <= i < |Prefixes(s)| ==> s[..i+1] == Prefixes(s)[i]
{
  if |s| == 0 then [] else Prefixes(s[..|s|-1]) + [s]
}
// </vc-helpers>

// <vc-spec>
method all_prefixes(s: string) returns (prefixes: seq<string>)

    ensures |prefixes| == |s|
    ensures forall i :: 0 <= i < |prefixes| ==> s[..i+1] == prefixes[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): delegate to helper function to construct all prefixes */
  prefixes := Prefixes(s);
}
// </vc-code>
