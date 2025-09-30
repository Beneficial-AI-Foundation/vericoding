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
predicate HasNaN(a: seq<Float>)
{
  exists i :: 0 <= i < |a| && a[i] == NaN
}

function FindMin(a: seq<Float>, idx: nat): Float
  requires |a| > 0
  requires idx <= |a|
  decreases |a| - idx
{
  if idx == |a| then
    a[|a| - 1]
  else if idx == 0 then
    FindMin(a, idx + 1)
  else
    var current := a[idx];
    var minRest := FindMin(a, idx + 1);
    if current == NaN || minRest == NaN then
      NaN
    else if FloatLessEq(current, minRest) then
      current
    else
      minRest
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
  if HasNaN(a) {
    result := NaN;
  } else {
    var i := 0;
    result := a[0];
    while i < |a|
      invariant 0 <= i <= |a|
      invariant exists j :: 0 <= j < |a| && a[j] == result
      invariant forall j :: 0 <= j < i ==> FloatLessEq(result, a[j])
    {
      if a[i] != NaN && FloatLessEq(a[i], result) {
        result := a[i];
      }
      i := i + 1;
    }
  }
}
// </vc-code>
