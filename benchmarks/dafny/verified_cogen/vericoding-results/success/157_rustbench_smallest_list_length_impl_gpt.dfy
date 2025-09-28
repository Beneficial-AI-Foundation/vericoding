// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
lemma MinLowerBounds(a: int, b: int)
  ensures min(a, b) <= a && min(a, b) <= b
{ }
// </vc-helpers>

// <vc-spec>
method SmallestListLength(lists: array<array<int>>) returns (result: int)
    requires lists.Length > 0
    ensures exists i :: 0 <= i < lists.Length && result == lists[i].Length
    ensures forall i :: 0 <= i < lists.Length ==> result <= lists[i].Length
// </vc-spec>
// <vc-code>
{
  var n := lists.Length;
  var idx := 0;
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant 0 <= idx < i
    invariant forall j :: 0 <= j < i ==> lists[idx].Length <= lists[j].Length
    decreases n - i
  {
    if lists[i].Length < lists[idx].Length {
      idx := i;
    }
    i := i + 1;
  }
  result := lists[idx].Length;
}
// </vc-code>
