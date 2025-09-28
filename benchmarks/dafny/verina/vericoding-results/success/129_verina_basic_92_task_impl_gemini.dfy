// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SwapArithmetic(x: int, y: int) returns (result: (int, int))
    ensures result.0 == y
    ensures result.1 == x
    ensures x != y ==> (result.0 != x && result.1 != y)
// </vc-spec>
// <vc-code>
{
  var new_x := x + y;
  var new_y := new_x - y;
  new_x := new_x - new_y;
  result := (new_x, new_y);
}
// </vc-code>
