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
// Helper function to check if any element in the sequence is NaN
predicate HasNaN(s: seq<Float>)
{
  exists i :: 0 <= i < |s| && s[i] == NaN
}

// Helper function to find the first NaN in a sequence
function FindNaN(s: seq<Float>): Float
  requires HasNaN(s)
  ensures FindNaN(s) == NaN
{
  if s[0] == NaN then NaN
  else FindNaN(s[1..])
}

// Helper function to find minimum when no NaN is present
function FindMinNoNaN(s: seq<Float>): Float
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> s[i] != NaN
  ensures exists i :: 0 <= i < |s| && s[i] == FindMinNoNaN(s)
  ensures forall i :: 0 <= i < |s| ==> FloatLessEq(FindMinNoNaN(s), s[i])
{
  if |s| == 1 then s[0]
  else
    var restMin := FindMinNoNaN(s[1..]);
    if FloatLessEq(s[0], restMin) then s[0] else restMin
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
    result := FindMinNoNaN(a);
  }
}
// </vc-code>
