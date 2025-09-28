// <vc-preamble>
// Method to return the shape (length) of a one-dimensional array
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Shape<T>(a: seq<T>) returns (result: nat)
  // No preconditions - shape is defined for all sequences
  ensures result == |a|  // The shape equals the length of the input sequence
// </vc-spec>
// <vc-code>
{
  result := |a|;
}
// </vc-code>
