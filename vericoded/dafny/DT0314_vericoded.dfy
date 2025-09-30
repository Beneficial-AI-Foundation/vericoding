// <vc-preamble>
/*
 * Implementation of numpy.floor functionality - returns the floor of each input element.
 * The floor of a real number x is the largest integer i such that i <= x.
 */

// Method that computes the floor of each element in a sequence
// Ghost predicate to check if a real number represents an integer
ghost predicate IsInteger(r: real)
{
  exists k: int {:trigger k as real} :: r == k as real
}

// Floor function (Dafny built-in)
function Floor(r: real): real
{
  r.Floor as real
}

// Ceiling function (Dafny built-in)
function Ceiling(r: real): real
{
  (-((-r).Floor)) as real
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method NumpyFloor(x: seq<real>) returns (result: seq<real>)
  // No preconditions - floor is defined for all real numbers
  ensures |result| == |x|
  // Each result element is the floor of the corresponding input element
  ensures forall i :: 0 <= i < |x| ==> result[i] == Floor(x[i])
  // Floor properties: result[i] <= x[i] and x[i] < result[i] + 1
  ensures forall i :: 0 <= i < |x| ==> result[i] <= x[i] < result[i] + 1.0
  // Result elements are integers (represented as reals)
  ensures forall i :: 0 <= i < |x| ==> IsInteger(result[i])
  // Largest integer property: no integer k exists such that result[i] < k <= x[i]
  ensures forall i :: 0 <= i < |x| ==> 
    forall k :: IsInteger(k) && result[i] < k ==> x[i] < k
  // Monotonicity: if x[i] <= x[j] then result[i] <= result[j]
  ensures forall i, j :: 0 <= i < |x| && 0 <= j < |x| && x[i] <= x[j] ==> 
    result[i] <= result[j]
  // Integer preservation: if x[i] is an integer, then result[i] = x[i]
  ensures forall i :: 0 <= i < |x| && IsInteger(x[i]) ==> result[i] == x[i]
  // Relationship with ceiling: result[i] = -ceiling(-x[i])
  ensures forall i :: 0 <= i < |x| ==> result[i] == -Ceiling(-x[i])
// </vc-spec>
// <vc-code>
{
  result := [];
  for i := 0 to |x|
    invariant 0 <= i <= |x|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == Floor(x[j])
    invariant forall j :: 0 <= j < i ==> result[j] <= x[j] < result[j] + 1.0
    invariant forall j :: 0 <= j < i ==> IsInteger(result[j])
    invariant forall j :: 0 <= j < i ==> forall k :: IsInteger(k) && result[j] < k ==> x[j] < k
    invariant forall j1, j2 :: 0 <= j1 < i && 0 <= j2 < i && x[j1] <= x[j2] ==> result[j1] <= result[j2]
    invariant forall j :: 0 <= j < i && IsInteger(x[j]) ==> result[j] == x[j]
    invariant forall j :: 0 <= j < i ==> result[j] == -Ceiling(-x[j])
  {
    result := result + [Floor(x[i])];
  }
}
// </vc-code>
