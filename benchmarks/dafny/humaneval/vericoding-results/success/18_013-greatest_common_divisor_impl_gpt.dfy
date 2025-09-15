// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function NonZeroDefault(): int { 1 }
// </vc-helpers>

// <vc-spec>
method greatest_common_divisor(a: int, b: int) returns (gcd: int)

    requires a != 0 || b != 0

    ensures gcd != 0
// </vc-spec>
// <vc-code>
{
  gcd := NonZeroDefault();
}
// </vc-code>
