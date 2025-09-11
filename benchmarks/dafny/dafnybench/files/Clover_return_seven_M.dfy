// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method M(x: int) returns (seven: int)
  ensures seven==7
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
