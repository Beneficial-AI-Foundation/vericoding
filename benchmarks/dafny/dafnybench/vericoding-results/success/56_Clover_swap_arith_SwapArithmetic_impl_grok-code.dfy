

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SwapArithmetic(X: int, Y: int) returns(x: int, y: int)
  ensures x==Y
  ensures y==X
// </vc-spec>
// <vc-code>
{
  var sum := X + Y;
  var diff := sum - Y;
  var temp := sum - diff;
  x := temp;
  y := diff;
}
// </vc-code>

