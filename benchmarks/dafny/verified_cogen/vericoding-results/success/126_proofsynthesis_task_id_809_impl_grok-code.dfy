// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsSmaller(arr1: array<int>, arr2: array<int>) returns (result: bool)
    requires arr1.Length == arr2.Length
    ensures result == (forall i :: 0 <= i < arr1.Length ==> arr1[i] > arr2[i])
// </vc-spec>
// <vc-code>
{
  var i := 0;
  result := true;
  while i < arr1.Length
    invariant 0 <= i <= arr1.Length
    invariant result <==> (forall k :: 0 <= k < i ==> arr1[k] > arr2[k])
  {
    if arr1[i] <= arr2[i] {
      result := false;
    }
    i := i + 1;
  }
}
// </vc-code>
