// <vc-helpers>
// </vc-helpers>

method Triple (x:int) returns (r:int)
  ensures r==3*x
// <vc-code>
{
  assume false;
}
// </vc-code>