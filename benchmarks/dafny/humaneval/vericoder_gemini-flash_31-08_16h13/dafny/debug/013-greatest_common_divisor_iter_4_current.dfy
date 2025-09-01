// recursive version should be more promising

// <vc-helpers>
function GCD(a: int, b: int): int
  requires a != 0 || b != 0
  ensures GCD(a, b) != 0
{
  if a == 0 then
    abs(b)
  else if b == 0 then
    abs(a)
  else if a == b then
    abs(a)
  else if a > b then
    GCD(a - b, b)
  else
    GCD(a, b - a)
}
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
  if a == 0 then {
    return abs(b);
  }
  if b == 0 then {
    return abs(a);
  }
  if a == b then {
    return abs(a);
  }
  if a > b then {
    return greatest_common_divisor(a - b, b);
  }
  return greatest_common_divisor(a, b - a);
}
// </vc-code>

