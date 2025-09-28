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
  if arr1.Length == 0 {
    result := true;
    return;
  }
  
  var i := 0;
  while i < arr1.Length
    invariant 0 <= i <= arr1.Length
    invariant forall j :: 0 <= j < i ==> arr1[j] > arr2[j]
  {
    if arr1[i] <= arr2[i] {
      result := false;
      return;
    }
    i := i + 1;
  }
  result := true;
}
// </vc-code>
