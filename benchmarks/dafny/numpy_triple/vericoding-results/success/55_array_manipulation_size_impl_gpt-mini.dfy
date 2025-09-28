// <vc-preamble>
// Method to return the number of elements in a sequence (vector)
// Corresponds to numpy.size() when called without an axis parameter
// </vc-preamble>

// <vc-helpers>
lemma SeqLengthNonNegative<T>(a: seq<T>)
  ensures |a| >= 0
{
  assert |a| >= 0;
}
// </vc-helpers>

// <vc-spec>
method size(a: seq<real>) returns (result: nat)
  // No preconditions - works on any sequence
  // Postcondition: result equals the length of the input sequence
  ensures result == |a|
// </vc-spec>
// <vc-code>
{
  result := |a|;
}
// </vc-code>
