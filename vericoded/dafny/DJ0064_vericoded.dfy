// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  min := list[0].Length;
  var i := 1;
  while i < list.Length
    invariant 1 <= i <= list.Length
    invariant min >= 0
    invariant forall j :: 0 <= j < i ==> min <= list[j].Length
    invariant exists j :: 0 <= j < i && min == list[j].Length
  {
    if list[i].Length < min {
      min := list[i].Length;
    }
    i := i + 1;
  }
}
// </vc-code>
