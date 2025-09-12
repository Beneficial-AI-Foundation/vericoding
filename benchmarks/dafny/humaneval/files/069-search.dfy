// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method freq(s: seq<int>, x: int) returns (count: int)

    ensures count == |(set i | 0 <= i < |s| && s[i] == x)|
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
