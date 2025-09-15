// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method greatest_common_divisor(a: int, b: int) returns (gcd: int)

    requires a != 0 || b != 0

    ensures gcd != 0
// </vc-spec>
// <vc-code>
{
  var x := if a >= 0 then a else -a;
  var y := if b >= 0 then b else -b;
  
  if x == 0 {
    gcd := y;
  } else if y == 0 {
    gcd := x;
  } else {
    while y != 0
      invariant x > 0 && y >= 0
    {
      var temp := y;
      y := x % y;
      x := temp;
    }
    gcd := x;
  }
}
// </vc-code>
