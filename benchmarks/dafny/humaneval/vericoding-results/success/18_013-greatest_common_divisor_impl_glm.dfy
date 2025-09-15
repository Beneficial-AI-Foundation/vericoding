// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function abs(x: int): int {
  if x < 0 then -x else x
}
// </vc-helpers>

// <vc-spec>
method greatest_common_divisor(a: int, b: int) returns (gcd: int)

    requires a != 0 || b != 0

    ensures gcd != 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): removed semicolon from loop invariant to fix deprecated warning */
  var x := abs(a);
  var y := abs(b);
  
  assert x != 0 || y != 0;
  
  while y != 0
    invariant x != 0 || y != 0
  {
    var r := x % y;
    x := y;
    y := r;
  }
  
  assert x != 0;
  gcd := x;
}
// </vc-code>
