// <vc-preamble>
/*
 * numpy.rollaxis: Roll the specified axis backwards, until it lies in a given position.
 * 
 * For 1D arrays, this is a no-op - it returns the input array unchanged.
 * This is because with only one axis (axis 0), there's nowhere to roll it to.
 * The axis and start parameters are ignored in the 1D case.
 * 
 * Note: This function is deprecated in favor of moveaxis, but we provide
 * the specification for completeness.
 */

// Method implementing numpy.rollaxis for 1D arrays
// For 1D arrays, rollaxis is the identity function since there's only one axis that cannot be moved
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method numpy_rollaxis(a: seq<real>, axis: int, start: int) returns (result: seq<real>)
  // No special preconditions for 1D rollaxis
  requires true
  // The result is identical to the input vector
  ensures result == a
  // The length is preserved
  ensures |result| == |a|
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
