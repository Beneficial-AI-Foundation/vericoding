// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method HasOnlyOneDistinctElement(arr: array<int>) returns (result: bool)
    ensures result == (forall i :: 1 <= i < arr.Length ==> arr[0] == arr[i])
// </vc-spec>
// <vc-code>
{
  if arr.Length == 0 {
    result := true;
    return;
  }
  
  var i := 1;
  while i < arr.Length
    invariant 1 <= i <= arr.Length
    invariant forall j :: 1 <= j < i ==> arr[0] == arr[j]
  {
    if arr[0] != arr[i] {
      result := false;
      return;
    }
    i := i + 1;
  }
  
  result := true;
}
// </vc-code>
