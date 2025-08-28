// <vc-helpers>
// No additional helpers or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method ComputeAvg(a: int, b: int) returns (avg:int)
  ensures avg == (a+b)/2
// </vc-spec>
// </vc-spec>

// <vc-code>
method ComputeAvgImpl(a: int, b: int) returns (avg: int)
  ensures avg == (a + b) / 2
{
  avg := (a + b) / 2;
}
// </vc-code>
