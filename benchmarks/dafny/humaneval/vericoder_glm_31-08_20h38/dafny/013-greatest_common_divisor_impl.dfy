// recursive version should be more promising

// <vc-helpers>
function gcd_nonneg(a: int, b: int): int
  requires a >= 0 && b >= 0 && (a != 0 || b != 0)
  ensures gcd_nonneg(a, b) > 0
  decreases b
{
  if b == 0 then a else gcd_nonneg(b, a % b)
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
  var a' := if a < 0 then -a else a;
  var b' := if b < 0 then -b else b;
  return gcd_nonneg(a', b');
}
// </vc-code>

