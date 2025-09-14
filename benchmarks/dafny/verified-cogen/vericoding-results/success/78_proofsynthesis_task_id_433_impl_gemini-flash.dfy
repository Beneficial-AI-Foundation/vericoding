// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsGreater(arr: array<int>, number: int) returns (result: bool)
    ensures result == (forall i :: 0 <= i < arr.Length ==> number > arr[i])
// </vc-spec>
// <vc-code>
{
  result := true;
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant result == (forall j :: 0 <= j < i ==> number > arr[j])
  {
    if number <= arr[i] {
      result := false;
      break;
    }
    i := i + 1;
  }
}
// </vc-code>
