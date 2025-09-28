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
{  var minSoFar := a[0];  var hasNaN: bool := false;  if a[0] == NaN {    hasNaN := true;  }  var j := 1;  while j < |a|    invariant 0 <= j <= |a|    invariant !hasNaN ==> (forall k :: 0 <= k < j ==> a[k] != NaN && FloatLessEq(minSoFar, a[k]))    invariant hasNaN ==> exists k :: 0 <= k < j && a[k] == NaN    invariant !hasNaN ==> exists k :: 0 <= k < j && a[k] == minSoFar  {    if a[j] == NaN {      hasNaN := true;    } else {      if FloatLessEq(a[j], minSoFar) {        minSoFar := a[j];      }    }    j := j + 1;  }  if hasNaN {    result := NaN;  } else {    result := minSoFar;  }  }
// </vc-code>
