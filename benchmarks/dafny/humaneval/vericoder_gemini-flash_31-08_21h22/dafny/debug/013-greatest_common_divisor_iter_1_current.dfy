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
  if b == 0 then
    return if a < 0 then -a else a;
  else
    return greatest_common_divisor(b, a % b);
}
// </vc-code>

