// <vc-preamble>
/*
 * numpy.isin: Element-wise test for membership in another array.
 * This file implements a Dafny specification for the numpy.isin function,
 * which performs element-wise membership testing between an input array
 * and a test elements array, returning a boolean array indicating membership.
 */
// </vc-preamble>

// <vc-helpers>

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
  result := [];
  var i := 0;
  while i < |element|
    invariant 0 <= i <= |element|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> 
      (result[k] <==> exists j :: 0 <= j < |test_elements| && element[k] == test_elements[j])
  {
    var found := false;
    var j := 0;
    while j < |test_elements|
      invariant 0 <= j <= |test_elements|
      invariant found <==> exists k :: 0 <= k < j && element[i] == test_elements[k]
    {
      if element[i] == test_elements[j] {
        found := true;
      }
      j := j + 1;
    }
    result := result + [found];
    i := i + 1;
  }
}
// </vc-code>
