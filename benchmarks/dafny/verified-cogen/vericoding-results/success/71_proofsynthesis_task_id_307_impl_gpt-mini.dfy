// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate InRange(i: int, n: int) { 0 <= i < n }
// </vc-helpers>

// <vc-spec>
method ListDeepClone(arr: array<int>) returns (copied: array<int>)
    ensures arr.Length == copied.Length
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] == copied[i]
// </vc-spec>
// <vc-code>
{
  var n := arr.Length;
  copied := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> copied[k] == arr[k]
  {
    copied[i] := arr[i];
    i := i + 1;
  }
}
// </vc-code>
