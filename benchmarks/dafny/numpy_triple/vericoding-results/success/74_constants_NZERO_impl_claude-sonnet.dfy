// <vc-preamble>
// Method that returns IEEE 754 negative zero
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method NZERO() returns (result: real)
  ensures result == 0.0
  // Basic arithmetic properties - negative zero behaves like positive zero in most operations
  ensures result + 0.0 == 0.0
  ensures result - 0.0 == 0.0  
  ensures result * 1.0 == 0.0
  // Multiplication preserves the zero value
  ensures result * 2.0 == 0.0
  // Division by non-zero gives zero (conceptual representation)
  ensures result / 1.0 == 0.0
  // Addition with other numbers
  ensures result + 1.0 == 1.0
  ensures result + (-1.0) == -1.0
  // Subtraction properties  
  ensures 1.0 - result == 1.0
  ensures (-1.0) - result == -1.0
  // Absolute value of negative zero is positive zero
  ensures (if result >= 0.0 then result else -result) == 0.0
// </vc-spec>
// <vc-code>
{
  result := 0.0;
}
// </vc-code>
