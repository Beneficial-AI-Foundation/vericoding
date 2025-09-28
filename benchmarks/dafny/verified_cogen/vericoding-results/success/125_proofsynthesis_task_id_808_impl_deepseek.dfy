// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ContainsK(arr: array<int>, k: int) returns (result: bool)
    ensures result == (exists i :: 0 <= i < arr.Length && arr[i] == k)
// </vc-spec>
// <vc-code>
{
  var index := 0;
  while index < arr.Length
    invariant 0 <= index <= arr.Length
    invariant !(exists i :: 0 <= i < index && arr[i] == k)
  {
    if arr[index] == k {
      result := true;
      return;
    }
    index := index + 1;
  }
  result := false;
}
// </vc-code>
