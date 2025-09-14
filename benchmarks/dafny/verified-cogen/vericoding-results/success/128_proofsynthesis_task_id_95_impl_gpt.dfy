// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
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
  var best: int := 0;
  var bestLen: int := list[0].Length;
  var i: int := 1;
  while i < list.Length
    invariant 0 <= i <= list.Length
    invariant 0 <= best < i
    invariant bestLen == list[best].Length
    invariant forall j :: 0 <= j < i ==> bestLen <= list[j].Length
  {
    if list[i].Length < bestLen {
      best := i;
      bestLen := list[i].Length;
    }
    i := i + 1;
  }
  min := bestLen;
}
// </vc-code>
