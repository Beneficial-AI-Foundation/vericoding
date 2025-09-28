// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ListDeepClone(arr: array<int>) returns (copied: array<int>)
    ensures arr.Length == copied.Length
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] == copied[i]
// </vc-spec>
// <vc-code>
{
  copied := new int[arr.Length];
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant copied.Length == arr.Length
    invariant forall j :: 0 <= j < i ==> copied[j] == arr[j]
  {
    copied[i] := arr[i];
    i := i + 1;
  }
}
// </vc-code>
