// <vc-preamble>
// </vc-preamble>

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
  assume {:axiom} false;
}
// </vc-code>
