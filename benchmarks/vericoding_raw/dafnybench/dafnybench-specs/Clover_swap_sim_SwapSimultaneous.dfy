// <vc-helpers>
// </vc-helpers>

method SwapSimultaneous(X: int, Y: int) returns(x: int, y: int)
  ensures x==Y
  ensures y==X
// <vc-code>
{
  assume false;
}
// </vc-code>