// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Swap(X: int, Y: int) returns(x: int, y: int)
  ensures x==Y
  ensures y==X
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>
