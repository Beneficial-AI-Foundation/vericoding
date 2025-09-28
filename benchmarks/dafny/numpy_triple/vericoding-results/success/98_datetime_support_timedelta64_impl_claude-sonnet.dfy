// <vc-preamble>
/*
 * TimeDelta64 implementation for representing time duration values as 64-bit integers
 * with associated time units, equivalent to numpy.timedelta64 functionality.
 */

// 64-bit signed integer type constraint
type int64 = i : int | -9223372036854775808 <= i <= 9223372036854775807

// Time unit enumeration representing different temporal granularities
datatype TimeUnit = 
  | Year        // Year unit ('Y')
  | Month       // Month unit ('M') 
  | Week        // Week unit ('W')
  | Day         // Day unit ('D')
  | Hour        // Hour unit ('h')
  | Minute      // Minute unit ('m')
  | Second      // Second unit ('s')
  | Millisecond // Millisecond unit ('ms')
  | Microsecond // Microsecond unit ('us')
  | Nanosecond  // Nanosecond unit ('ns')
  | Picosecond  // Picosecond unit ('ps')
  | Femtosecond // Femtosecond unit ('fs')
  | Attosecond  // Attosecond unit ('as')

// Time duration structure containing a 64-bit integer value and time unit
datatype TimeDelta64 = TimeDelta64(value: int64, unit: TimeUnit)

// Creates a TimeDelta64 object from a numeric value and time unit
// The value must be within 64-bit signed integer bounds
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method timedelta64(value: int, unit: TimeUnit) returns (result: TimeDelta64)
  requires -9223372036854775808 <= value <= 9223372036854775807
  ensures result.value == value
  ensures result.unit == unit
  ensures -9223372036854775808 <= result.value <= 9223372036854775807
// </vc-spec>
// <vc-code>
{
  result := TimeDelta64(value, unit);
}
// </vc-code>
