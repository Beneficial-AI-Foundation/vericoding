// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method SmallestListLength(lists: array<array<int>>) returns (result: int)
    requires lists.Length > 0
    ensures exists i :: 0 <= i < lists.Length && result == lists[i].Length
    ensures forall i :: 0 <= i < lists.Length ==> result <= lists[i].Length
// </vc-spec>
// <vc-code>
{
  var minIdx := 0;
  var i := 1;
  while i < lists.Length
    invariant 1 <= i <= lists.Length
    invariant 0 <= minIdx < i
    invariant forall k :: 0 <= k < i ==> lists[minIdx].Length <= lists[k].Length
  {
    if lists[i].Length < lists[minIdx].Length {
      minIdx := i;
    }
    i := i + 1;
  }
  result := lists[minIdx].Length;
}
// </vc-code>
