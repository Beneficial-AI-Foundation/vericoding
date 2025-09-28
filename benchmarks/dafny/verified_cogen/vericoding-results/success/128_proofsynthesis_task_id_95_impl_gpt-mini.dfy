// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function minInt(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method SmallestListLength(list: array<array<int>>) returns (min: int)
    requires list.Length > 0
    ensures min >= 0
    ensures forall i :: 0 <= i < list.Length ==> min <= list[i].Length
    ensures exists i :: 0 <= i < list.Length && min == list[i].Length
// </vc-spec>
// <vc-code>
{
  var n := list.Length;
  var idx := 0;
  var m := list[0].Length;
  var i := 1;
  while i < n
    invariant 1 <= n
    invariant 0 <= i <= n
    invariant m >= 0
    invariant forall j :: 0 <= j < i ==> m <= list[j].Length
    invariant exists k :: 0 <= k < i && m == list[k].Length
    decreases n - i
  {
    if list[i].Length < m {
      m := list[i].Length;
      idx := i;
    }
    i := i + 1;
  }
  min := m;
}
// </vc-code>
