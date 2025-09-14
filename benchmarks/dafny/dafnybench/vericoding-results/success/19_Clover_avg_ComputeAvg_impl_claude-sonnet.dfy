

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ComputeAvg(a: int, b: int) returns (avg:int)
  ensures avg == (a+b)/2
// </vc-spec>
// <vc-code>
{
  avg := (a + b) / 2;
}
// </vc-code>

