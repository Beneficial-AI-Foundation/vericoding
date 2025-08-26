// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Fact(x: int) returns (y: int)
  requires x >= 0;
// </vc-spec>
// <vc-code>
{
  if x == 0 {
    y := 1;
  } else {
    y := 1;
    var i := 1;
    while i <= x
      invariant 1 <= i <= x + 1
      invariant y >= 1
    {
      y := y * i;
      i := i + 1;
    }
  }
}
// </vc-code>