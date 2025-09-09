/*
function_signature: def greatest_common_divisor(a: int, b: int) -> int
Return a greatest common divisor of two integers a and b

// recursive version should be more promising
*/

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method greatest_common_divisor(a: int, b: int) returns (gcd: int)

    requires a != 0 || b != 0

    ensures gcd != 0
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
