// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function abs(x: int): int { if x < 0 then -x else x }
// </vc-helpers>

// <vc-spec>
method greatest_common_divisor(a: int, b: int) returns (gcd: int)

    requires a != 0 || b != 0

    ensures gcd != 0
// </vc-spec>
// <vc-code>
{
  var x := abs(a);
  var y := abs(b);

  while y != 0
    invariant x >= 0 && y >= 0
    invariant x > 0 || y > 0
  {
    var temp := y;
    y := x % y;
    x := temp;
  }
  gcd := x;
}
// </vc-code>
