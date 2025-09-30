// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SmallestListLength(lists: array<array<int>>) returns (result: int)
    requires lists.Length > 0
    ensures exists i :: 0 <= i < lists.Length && result == lists[i].Length
    ensures forall i :: 0 <= i < lists.Length ==> result <= lists[i].Length
// </vc-spec>
// <vc-code>
{
  result := lists[0].Length;
  var i := 1;
  while i < lists.Length
    invariant 1 <= i <= lists.Length
    invariant exists j :: 0 <= j < i && result == lists[j].Length
    invariant forall j :: 0 <= j < i ==> result <= lists[j].Length
  {
    if lists[i].Length < result {
      result := lists[i].Length;
    }
    i := i + 1;
  }
}
// </vc-code>
