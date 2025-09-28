// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method HasOnlyOneDistinctElement(arr: array<int>) returns (result: bool)
    ensures result == (forall i :: 1 <= i < arr.Length ==> arr[0] == arr[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): handle small arrays to establish loop invariant */
{
  if arr.Length <= 1 {
    result := true;
    return;
  }

  result := true;
  var i := 1;
  while i < arr.Length
    invariant arr.Length >= 2
    invariant 1 <= i <= arr.Length
    invariant forall k :: 1 <= k < i ==> arr[0] == arr[k]
  {
    if arr[i] != arr[0] {
      result := false;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>
