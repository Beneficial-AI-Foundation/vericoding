// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
predicate IsValidIndex(i: int, len: int) { 0 <= i < len }
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
    decreases arr.Length - i
  {
    copied[i] := arr[i];
    i := i + 1;
  }
}
// </vc-code>
