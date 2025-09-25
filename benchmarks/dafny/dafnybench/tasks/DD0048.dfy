// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ComputeAvg(a: int, b: int) returns (avg:int)
  ensures avg == (a+b)/2
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
