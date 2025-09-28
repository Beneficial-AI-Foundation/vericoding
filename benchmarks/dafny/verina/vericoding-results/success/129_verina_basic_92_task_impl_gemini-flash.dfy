// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Add(a: int, b: int): int { a + b }

function Subtract(a: int, b: int): int { a - b }
// </vc-helpers>

// <vc-spec>
method SwapArithmetic(x: int, y: int) returns (result: (int, int))
    ensures result.0 == y
    ensures result.1 == x
    ensures x != y ==> (result.0 != x && result.1 != y)
// </vc-spec>
// <vc-code>
{
  var a := x;
  var b := y;
  a := a + b;
  b := a - b;
  a := a - b;
  result := (a, b);
}
// </vc-code>
