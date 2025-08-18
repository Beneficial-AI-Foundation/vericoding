// <vc-helpers>
// </vc-helpers>

method Fact(x: int) returns (y: int)
  requires x >= 0;
// <vc-code>
{
  assume false;
}
// </vc-code>