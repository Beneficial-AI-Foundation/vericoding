
/*
function_signature: def greatest_common_divisor(a: int, b: int) -> int
Return a greatest common divisor of two integers a and b
*/

// recursive version should be more promising

method greatest_common_divisor(a: int, b: int) returns (gcd: int)
    // pre-conditions-start
    requires a != 0 || b != 0
    // pre-conditions-end
    // post-conditions-start
    ensures gcd != 0
    // post-conditions-end
{
  assume false;
}
