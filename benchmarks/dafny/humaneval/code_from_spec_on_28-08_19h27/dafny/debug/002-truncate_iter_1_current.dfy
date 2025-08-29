// <vc-helpers>
// </vc-helpers>

// <vc-description>
/*
function_signature: def truncate_number(number: float) -> float
Given a positive floating point number, it can be decomposed into and integer part (largest integer smaller than given number) and decimals (leftover part always smaller than 1).
*/
// </vc-description>

// <vc-spec>
method truncate_number(number: real) returns (result: real)
  requires number >= 0.0
  ensures result >= 0.0
  ensures result <= number
  ensures number - result < 1.0
  ensures result == real(number as int)
// </vc-spec>
// <vc-code>
{
  result := real(number as int);
}
// </vc-code>
