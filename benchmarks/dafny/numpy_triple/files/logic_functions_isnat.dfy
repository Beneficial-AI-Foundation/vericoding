// <vc-preamble>
/*
 * Test element-wise for NaT (not a time) and return result as a boolean array.
 * 
 * This function checks each element of a datetime64 array to determine if it
 * represents NaT (Not a Time), which is the datetime equivalent of NaN.
 * Returns true for NaT values and false for all valid datetime values.
 */

// DateTime64 type representing either a valid datetime or NaT (Not a Time)
datatype DateTime64 = Valid(time: real) | NaT

// Test element-wise for NaT values in datetime64 sequence
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method isnat(x: seq<DateTime64>) returns (result: seq<bool>)
  // Result preserves shape: output sequence has same length as input
  ensures |result| == |x|
  // NaT detection: result[i] = true iff x[i] is NaT
  ensures forall i :: 0 <= i < |x| ==> result[i] == (x[i] == NaT)
  // Valid datetime detection: result[i] = false iff x[i] is a valid datetime
  ensures forall i :: 0 <= i < |x| ==> result[i] == false <==> x[i].Valid?
  // Exhaustive coverage: every element is either NaT or a valid datetime
  ensures forall i :: 0 <= i < |x| ==> x[i].NaT? || x[i].Valid?
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
