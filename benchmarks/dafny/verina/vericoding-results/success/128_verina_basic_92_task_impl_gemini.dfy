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
  var x_new := x + y;
  var y_new := x_new - y;
  var x_final := x_new - y_new;
  result := (x_final, y_new);
}
// </vc-code>
