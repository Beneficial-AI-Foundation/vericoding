// <vc-preamble>
// Vector type representing a sequence of floating-point numbers
// Note: Unlike Lean's Vector Float n, Dafny sequences are variable-size
type Vector = seq<real>

/**
 * AsAnyArray method that returns the input vector unchanged when it's already an ndarray.
 * This captures the key property of numpy.asanyarray: when given an ndarray,
 * it returns the same array without copying.
 */
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method AsAnyArray(a: Vector, ghost n: nat) returns (result: Vector)
  requires |a| == n  // Input has fixed size n
  ensures |result| == n  // Output preserves the fixed size
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |a| ==> result[i] == a[i]
// </vc-spec>
// <vc-code>
{
  result := a;
}
// </vc-code>
