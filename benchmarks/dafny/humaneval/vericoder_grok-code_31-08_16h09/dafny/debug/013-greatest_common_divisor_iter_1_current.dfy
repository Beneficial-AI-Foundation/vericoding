// recursive version should be more promising

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method greatest_common_divisor(a: int, b: int) returns (gcd: int)
    // pre-conditions-start
    requires a != 0 || b != 0
    // pre-conditions-end
    // post-conditions-start
    ensures gcd != 0
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var x := a;
  var y := b;
  while y != 0
    invariant x != 0 || y != 0
  {
    var temp := y;
    y := x % y;
    x := temp;
  }
  gcd := if x < 0 then -x else x;
}
// </vc-code>

