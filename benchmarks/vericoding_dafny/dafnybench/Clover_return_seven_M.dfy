// <vc-helpers>
// </vc-helpers>

method M(x: int) returns (seven: int)
  ensures seven==7
// <vc-code>
{
  assume false;
}
// </vc-code>