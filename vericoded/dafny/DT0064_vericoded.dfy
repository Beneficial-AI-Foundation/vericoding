// <vc-preamble>
// Method that reshapes a 1D array to another 1D array of the same size
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method reshape(a: seq<real>, newSize: nat) returns (result: seq<real>)
  // The new size must equal the original size (no data is lost or added)
  requires |a| == newSize
  // The result has the specified new size
  ensures |result| == newSize
  // All elements are preserved in their original linear order
  ensures forall i :: 0 <= i < newSize ==> result[i] == a[i]
// </vc-spec>
// <vc-code>
{
  result := a;
}
// </vc-code>
