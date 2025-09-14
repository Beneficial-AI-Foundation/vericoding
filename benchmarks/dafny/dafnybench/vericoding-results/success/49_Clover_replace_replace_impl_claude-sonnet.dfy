

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method replace(arr: array<int>, k: int)
  modifies arr
  ensures forall i :: 0 <= i < arr.Length ==> old(arr[i]) > k ==> arr[i] == -1
  ensures forall i :: 0 <= i < arr.Length ==> old(arr[i]) <= k ==> arr[i] == old(arr[i])
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall j :: 0 <= j < i ==> old(arr[j]) > k ==> arr[j] == -1
    invariant forall j :: 0 <= j < i ==> old(arr[j]) <= k ==> arr[j] == old(arr[j])
    invariant forall j :: i <= j < arr.Length ==> arr[j] == old(arr[j])
  {
    if arr[i] > k {
      arr[i] := -1;
    }
    i := i + 1;
  }
}
// </vc-code>

