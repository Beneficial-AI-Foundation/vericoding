// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method unique(arr: seq<int>) returns (result: seq<int>)
    ensures |result| <= |arr|
    // Result is sorted in ascending order
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    // Every element in result exists in the input array
    ensures forall i :: 0 <= i < |result| ==> result[i] in arr
    // All elements in result are unique (no duplicates)
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
    // Every element in input array appears in the result
    ensures forall x :: x in arr ==> x in result
    // Equivalently: every index in input has its value represented in result
    ensures forall i :: 0 <= i < |arr| ==> arr[i] in result
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
