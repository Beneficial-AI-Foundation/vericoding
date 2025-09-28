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
/* helper modified by LLM (iteration 4): removed problematic SpecMin function */
function FloatMin(x: Float, y: Float): Float
{
  match (x, y) {
    case (NaN, _) => NaN
    case (_, NaN) => NaN
    case (NegInf, _) => NegInf
    case (_, NegInf) => NegInf
    case (PosInf, y) => y
    case (x, PosInf) => x
    case (Float(a), Float(b)) => if a <= b then Float(a) else Float(b)
  }
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
  /* code modified by LLM (iteration 4): replaced SpecMin invariant with explicit properties */
  var current_min := a[0];
  var i := 1;
  while i < |a|
    invariant 1 <= i <= |a|
    invariant (exists k :: 0 <= k < i && a[k] == NaN) <==> (current_min == NaN)
    invariant (forall k :: 0 <= k < i ==> a[k] != NaN) ==> 
                ((exists j :: 0 <= j < i && a[j] == current_min) &&
                (forall j :: 0 <= j < i ==> FloatLessEq(current_min, a[j])))
  {
    current_min := FloatMin(current_min, a[i]);
    i := i + 1;
  }
  result := current_min;
}
// </vc-code>
