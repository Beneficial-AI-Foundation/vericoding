// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): No helpers needed */
// </vc-helpers>

// <vc-spec>
method SmallestListLength(list: array<array<int>>) returns (min: int)
    requires list.Length > 0
    ensures min >= 0
    ensures forall i :: 0 <= i < list.Length ==> min <= list[i].Length
    ensures exists i :: 0 <= i < list.Length && min == list[i].Length
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed compilation by adding an if-else for the loop invariant */
{
  min := list[0].Length;
  var i := 1;
  while i < list.Length
    invariant 0 <= i <= list.Length
    invariant forall k :: 0 <= k < i ==> min <= list[k].Length
    invariant exists k :: 0 <= k < i && min == list[k].Length
  {
    if list[i].Length < min {
      min := list[i].Length;
    }
    i := i + 1;
  }
}
// </vc-code>
