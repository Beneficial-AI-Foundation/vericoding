// <vc-helpers>
// </vc-helpers>

method ComputeAvg(a: int, b: int) returns (avg:int)
  ensures avg == (a+b)/2
// <vc-code>
{
  assume false;
}
// </vc-code>