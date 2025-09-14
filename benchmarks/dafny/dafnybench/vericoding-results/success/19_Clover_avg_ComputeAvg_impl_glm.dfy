

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ComputeAvg(a: int, b: int) returns (avg:int)
  ensures avg == (a+b)/2
// </vc-spec>
// <vc-code>
{
  return (a+b)/2;
}
// </vc-code>

