// <vc-preamble>
/*
 * numpy.isin: Element-wise test for membership in another array.
 * This file implements a Dafny specification for the numpy.isin function,
 * which performs element-wise membership testing between an input array
 * and a test elements array, returning a boolean array indicating membership.
 */
// </vc-preamble>

// <vc-helpers>
function contains(a: seq<real>, x: real): bool { exists j :: 0 <= j < |a| && a[j] == x }
// </vc-helpers>

// <vc-spec>
method numpy_isin(element: seq<real>, test_elements: seq<real>) returns (result: seq<bool>)
    // No special preconditions needed
    requires true
    // Result has same length as input element array
    ensures |result| == |element|
    // Each result element indicates whether corresponding input element is in test_elements
    ensures forall i :: 0 <= i < |element| ==> 
        (result[i] <==> exists j :: 0 <= j < |test_elements| && element[i] == test_elements[j])
// </vc-spec>
// <vc-code>
{
  var n := |element|;
  var resArr := new bool[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> resArr[k] == contains(test_elements, element[k])
  {
    resArr[i] := contains(test_elements, element[i]);
    i := i + 1;
  }
  result := resArr[..];
}
// </vc-code>
