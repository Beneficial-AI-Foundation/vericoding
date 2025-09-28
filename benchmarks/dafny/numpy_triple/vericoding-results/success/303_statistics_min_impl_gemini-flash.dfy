// <vc-preamble>
/*
 * Dafny specification for numpy.min function - returns the minimum element of a non-empty array.
 * This is an alias for numpy.amin that finds the smallest value among all elements in the input array.
 */

// Float datatype to represent floating-point numbers with special values
datatype Float = Float(value: real) | NaN | PosInf | NegInf

// Method to find the minimum element in a non-empty sequence of floating-point numbers
// Helper predicate for floating-point comparison
predicate FloatLessEq(x: Float, y: Float)
{
  match (x, y)
    case (NaN, _) => false
    case (_, NaN) => false
    case (NegInf, _) => true
    case (_, PosInf) => true
    case (PosInf, _) => false
    case (_, NegInf) => false
    case (Float(a), Float(b)) => a <= b
}
// </vc-preamble>

// <vc-helpers>
function minFloat(x: Float, y: Float): Float
{
  if (x == NaN || y == NaN) then NaN
  else if (FloatLessEq(x, y)) then x
  else y
}
// </vc-helpers>

// <vc-spec>
method min(a: seq<Float>) returns (result: Float)
  // Precondition: input array must be non-empty
  requires |a| > 0
  // Postcondition: if any element is NaN, result is NaN
  ensures (exists i :: 0 <= i < |a| && a[i] == NaN) ==> result == NaN
  // Postcondition: if no NaN present, result is an actual element from the input array
  ensures (forall i :: 0 <= i < |a| ==> a[i] != NaN) ==> (exists i :: 0 <= i < |a| && a[i] == result)
  // Postcondition: if no NaN present, result is less than or equal to all elements in the array
  ensures (forall i :: 0 <= i < |a| ==> a[i] != NaN) ==> (forall i :: 0 <= i < |a| ==> FloatLessEq(result, a[i]))
// </vc-spec>
// <vc-code>
{
  var currentMin: Float := a[0];
  var i: int := 1;

  while i < |a|
    invariant 1 <= i <= |a|
    invariant (exists k :: 0 <= k < i && a[k] == NaN) ==> currentMin == NaN
    invariant (forall k :: 0 <= k < i ==> a[k] != NaN) ==> (exists k :: 0 <= k < i && a[k] == currentMin)
    invariant (forall k :: 0 <= k < i ==> a[k] != NaN) ==> (forall k :: 0 <= k < i ==> FloatLessEq(currentMin, a[k]))
  {
    currentMin := minFloat(currentMin, a[i]);
    i := i + 1;
  }
  result := currentMin;
}
// </vc-code>
